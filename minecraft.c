#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <float.h>
#include <windows.h>
#include <string.h>
#include <time.h>

#define X_PIXELS 626
#define Y_PIXELS 169
#define X_BLOCKS 512
#define Y_BLOCKS 512
#define Z_BLOCKS 256
#define EYE_HEIGHT 1.5f
#define VIEW_HEIGHT 0.7f
#define VIEW_WIDTH 1.0f
#define BLOCK_BORDER_SIZE 0.05f
#define MOVE_SPEED 6.0f
#define VIEW_SPEED 3.0f
#define FRAME_DELAY_MS 16
#define ACTION_DELAY_MS 150
#define TERRAIN_SCALE 0.18f
#define TERRAIN_BASE_HEIGHT 3.0f
#define TERRAIN_VARIATION 4.0f
#define SEA_LEVEL -100
#define TREE_CHANCE 0.01f
#define TREE_MAX_HEIGHT 3
#define TREE_CANOPY_RADIUS 2
#define TERRAIN_OCTAVES 4

static const float MAX_DISTANCE = 25.0f;

typedef struct { float x; float y; float z; } vect;
typedef struct { float psi; float phi; } vect2;
typedef struct { vect pos; vect2 view; } player_pos_view;

static HANDLE hStdout;
static HANDLE hStdin;
static DWORD oldOutMode;
static DWORD oldInMode;
static CONSOLE_CURSOR_INFO oldCursorInfo;
static int console_ready = 0;

static unsigned char keystate[256];
static CHAR_INFO* frame_buffer = NULL;
static COORD frame_size = { X_PIXELS, Y_PIXELS };
static SMALL_RECT frame_rect = { 0, 0, X_PIXELS - 1, Y_PIXELS - 1 };
static DWORD last_place_tick = 0;
static DWORD last_break_tick = 0;
static unsigned int world_seed = 0;

static inline size_t block_offset(int x, int y, int z) {
    return ((size_t)z * (size_t)Y_BLOCKS + (size_t)y) * (size_t)X_BLOCKS + (size_t)x;
}

static inline char block_get(const char* blocks, int x, int y, int z) {
    return blocks[block_offset(x, y, z)];
}

static inline void block_set(char* blocks, int x, int y, int z, char value) {
    blocks[block_offset(x, y, z)] = value;
}

static void ensure_frame_buffer(void) {
    if (!frame_buffer) {
        frame_buffer = (CHAR_INFO*)calloc((size_t)X_PIXELS * (size_t)Y_PIXELS, sizeof(CHAR_INFO));
    }
}

static inline float lerp(float a, float b, float t) {
    return a + (b - a) * t;
}

static inline float smoothstep(float t) {
    return t * t * (3.0f - 2.0f * t);
}

static unsigned int hash_coords(int x, int y, unsigned int seed) {
    unsigned int h = (unsigned int)(x * 374761393 + y * 668265263);
    h ^= seed + 0x9E3779B9u + (h << 6) + (h >> 2);
    h ^= (h >> 13);
    h *= 1274126177u;
    return h;
}

static float rand01(int x, int y, unsigned int seed) {
    return (float)(hash_coords(x, y, seed) & 0xFFFFFFu) / (float)0xFFFFFFu;
}

static float value_noise(float x, float y, unsigned int seed) {
    int x0 = (int)floorf(x);
    int y0 = (int)floorf(y);
    int x1 = x0 + 1;
    int y1 = y0 + 1;

    float sx = smoothstep(x - (float)x0);
    float sy = smoothstep(y - (float)y0);

    float n00 = rand01(x0, y0, seed);
    float n10 = rand01(x1, y0, seed);
    float n01 = rand01(x0, y1, seed);
    float n11 = rand01(x1, y1, seed);

    float ix0 = lerp(n00, n10, sx);
    float ix1 = lerp(n01, n11, sx);
    return lerp(ix0, ix1, sy);
}

static float fractal_noise(float x, float y, unsigned int seed) {
    float total = 0.0f;
    float amplitude = 1.0f;
    float frequency = 1.0f;
    float max_amplitude = 0.0f;

    for (int octave = 0; octave < TERRAIN_OCTAVES; ++octave) {
        float noise = value_noise(x * frequency, y * frequency, seed + (unsigned int)(octave * 97));
        total += noise * amplitude;
        max_amplitude += amplitude;
        amplitude *= 0.5f;
        frequency *= 2.0f;
    }

    return (max_amplitude > 0.0f) ? total / max_amplitude : 0.0f;
}

static inline vect vect_add(vect a, vect b) { return (vect){ a.x + b.x, a.y + b.y, a.z + b.z }; }
static inline vect vect_sub(vect a, vect b) { return (vect){ a.x - b.x, a.y - b.y, a.z - b.z }; }
static inline vect vect_scale(float s, vect v) { return (vect){ s * v.x, s * v.y, s * v.z }; }
static inline void vect_normalize(vect* v) {
    float len = sqrtf(v->x * v->x + v->y * v->y + v->z * v->z);
    if (len > 0.0001f) {
        v->x /= len;
        v->y /= len;
        v->z /= len;
    }
}
static inline float clampf(float v, float min, float max) {
    if (v < min) return min;
    if (v > max) return max;
    return v;
}
static inline int clamp_index(int v, int max) {
    if (v < 0) return 0;
    if (v >= max) return max - 1;
    return v;
}
static vect angles_to_vect(vect2 angles) {
    vect dir = {
        cosf(angles.psi) * cosf(angles.phi),
        cosf(angles.psi) * sinf(angles.phi),
        sinf(angles.psi)
    };
    vect_normalize(&dir);
    return dir;
}

static void init_console(void) {
    hStdout = GetStdHandle(STD_OUTPUT_HANDLE);
    hStdin = GetStdHandle(STD_INPUT_HANDLE);
    if (hStdout == INVALID_HANDLE_VALUE || hStdin == INVALID_HANDLE_VALUE) {
        return;
    }

    ensure_frame_buffer();

    frame_size.X = X_PIXELS;
    frame_size.Y = Y_PIXELS;
    frame_rect.Left = 0;
    frame_rect.Top = 0;
    frame_rect.Right = X_PIXELS - 1;
    frame_rect.Bottom = Y_PIXELS - 1;

    COORD buffer_size = { X_PIXELS, Y_PIXELS };
    SetConsoleScreenBufferSize(hStdout, buffer_size);

    SMALL_RECT window = { 0, 0, X_PIXELS - 1, Y_PIXELS - 1 };
    SetConsoleWindowInfo(hStdout, TRUE, &window);

    SetConsoleOutputCP(CP_UTF8);

    if (GetConsoleMode(hStdout, &oldOutMode)) {
        DWORD outMode = oldOutMode | ENABLE_VIRTUAL_TERMINAL_PROCESSING;
        SetConsoleMode(hStdout, outMode);
    }
    if (GetConsoleMode(hStdin, &oldInMode)) {
        DWORD inMode = oldInMode;
        inMode |= ENABLE_EXTENDED_FLAGS;
        inMode &= ~(ENABLE_ECHO_INPUT | ENABLE_LINE_INPUT | ENABLE_QUICK_EDIT_MODE);
        SetConsoleMode(hStdin, inMode);
    }
    if (GetConsoleCursorInfo(hStdout, &oldCursorInfo)) {
        CONSOLE_CURSOR_INFO cursorInfo = oldCursorInfo;
        cursorInfo.bVisible = FALSE;
        SetConsoleCursorInfo(hStdout, &cursorInfo);
    }
    console_ready = 1;
}

static void restore_console(void) {
    if (!console_ready) return;
    SetConsoleMode(hStdout, oldOutMode);
    SetConsoleMode(hStdin, oldInMode);
    SetConsoleCursorInfo(hStdout, &oldCursorInfo);
    console_ready = 0;
}

static void process_input(void) {
    memset(keystate, 0, sizeof(keystate));

    const int tracked[] = { 'W', 'A', 'S', 'D', 'I', 'J', 'K', 'L', 'Q', 'X' };
    const size_t tracked_count = sizeof(tracked) / sizeof(tracked[0]);

    for (size_t i = 0; i < tracked_count; ++i) {
        int key = tracked[i];
        int down = (GetAsyncKeyState(key) & 0x8000) != 0;
        keystate[key] = (unsigned char)down;
        int lower = key + ('a' - 'A');
        if (lower >= 0 && lower < 256) {
            keystate[lower] = (unsigned char)down;
        }
    }

    keystate[' '] = (unsigned char)((GetAsyncKeyState(VK_SPACE) & 0x8000) != 0);
}

static int is_key_pressed(int key) {
    unsigned char idx = (unsigned char)key;
    if (key >= 'A' && key <= 'Z') {
        return keystate[idx] || keystate[idx + ('a' - 'A')];
    }
    if (key >= 'a' && key <= 'z') {
        return keystate[idx] || keystate[idx - ('a' - 'A')];
    }
    return keystate[idx];
}

static char** init_picture(void) {
    char** picture = (char**)malloc(Y_PIXELS * sizeof(char*));
    for (int y = 0; y < Y_PIXELS; ++y) {
        picture[y] = (char*)malloc(X_PIXELS * sizeof(char));
        memset(picture[y], ' ', X_PIXELS);
    }
    return picture;
}

static float** init_depth(void) {
    float** depth = (float**)malloc(Y_PIXELS * sizeof(float*));
    for (int y = 0; y < Y_PIXELS; ++y) {
        depth[y] = (float*)malloc(X_PIXELS * sizeof(float));
        for (int x = 0; x < X_PIXELS; ++x) depth[y][x] = MAX_DISTANCE;
    }
    return depth;
}

static char* init_blocks(void) {
    size_t total = (size_t)X_BLOCKS * (size_t)Y_BLOCKS * (size_t)Z_BLOCKS;
    char* blocks = (char*)malloc(total * sizeof(char));
    if (!blocks) {
        return NULL;
    }
    memset(blocks, ' ', total);
    return blocks;
}

static void free_blocks(char* blocks) {
    free(blocks);
}

static void generate_tree(char* blocks, int x, int y, int base_z, unsigned int seed) {
    if (base_z + 1 >= Z_BLOCKS) return;

    int extra = (int)(rand01(x, y, seed + 2011u) * (float)(TREE_MAX_HEIGHT + 1));
    int trunk_height = 2 + extra;
    if (base_z + trunk_height >= Z_BLOCKS) {
        trunk_height = Z_BLOCKS - base_z - 1;
    }
    if (trunk_height <= 0) return;

    for (int i = 1; i <= trunk_height; ++i) {
        int z = base_z + i;
        block_set(blocks, x, y, z, '|');
    }

    int top_z = base_z + trunk_height;
    int canopy_layers = 2;
    for (int layer = 0; layer < canopy_layers; ++layer) {
        int z = top_z + layer;
        if (z >= Z_BLOCKS) break;
        int radius = TREE_CANOPY_RADIUS - layer;
        if (radius < 1) radius = 1;

        for (int dy = -radius; dy <= radius; ++dy) {
            int ny = y + dy;
            if (ny < 0 || ny >= Y_BLOCKS) continue;
            for (int dx = -radius; dx <= radius; ++dx) {
                int nx = x + dx;
                if (nx < 0 || nx >= X_BLOCKS) continue;
                if (abs(dx) + abs(dy) > radius + 1) continue;
                if (block_get(blocks, nx, ny, z) == ' ') {
                    block_set(blocks, nx, ny, z, '&');
                }
            }
        }
    }
}

static void generate_world(char* blocks, unsigned int seed) {
    for (int y = 0; y < Y_BLOCKS; ++y) {
        for (int x = 0; x < X_BLOCKS; ++x) {
            float nx = (float)x * TERRAIN_SCALE;
            float ny = (float)y * TERRAIN_SCALE;
            float elevation = fractal_noise(nx, ny, seed);

            int ground_height = (int)lroundf(TERRAIN_BASE_HEIGHT + elevation * TERRAIN_VARIATION);
            if (ground_height < 0) ground_height = 0;
            if (ground_height >= Z_BLOCKS) ground_height = Z_BLOCKS - 1;

            char surface_block = (ground_height >= SEA_LEVEL) ? '=' : '@';
            for (int z = 0; z <= ground_height && z < Z_BLOCKS; ++z) {
                if (z == ground_height) {
                    block_set(blocks, x, y, z, surface_block);
                } else if (ground_height - z >= 2) {
                    block_set(blocks, x, y, z, '#');
                } else {
                    block_set(blocks, x, y, z, '@');
                }
            }

            if (ground_height < SEA_LEVEL) {
                for (int z = ground_height + 1; z <= SEA_LEVEL && z < Z_BLOCKS; ++z) {
                    block_set(blocks, x, y, z, '~');
                }
            } else {
                float tree_roll = rand01(x, y, seed + 1337u);
                if (tree_roll < TREE_CHANCE) {
                    generate_tree(blocks, x, y, ground_height, seed);
                }
            }
        }
    }
}

static player_pos_view init_posview(void) {
    player_pos_view posview;
    posview.pos.x = X_BLOCKS / 2.0f;
    posview.pos.y = Y_BLOCKS / 2.0f;
    posview.pos.z = 4.0f + EYE_HEIGHT;
    posview.view.phi = 0.0f;
    posview.view.psi = 0.0f;
    return posview;
}

static int ray_outside(vect pos) {
    return pos.x < 0.0f || pos.y < 0.0f || pos.z < 0.0f ||
           pos.x >= (float)X_BLOCKS || pos.y >= (float)Y_BLOCKS || pos.z >= (float)Z_BLOCKS;
}

static int on_block_border(vect pos) {
    int cnt = 0;
    if (fabsf(pos.x - roundf(pos.x)) < BLOCK_BORDER_SIZE) cnt++;
    if (fabsf(pos.y - roundf(pos.y)) < BLOCK_BORDER_SIZE) cnt++;
    if (fabsf(pos.z - roundf(pos.z)) < BLOCK_BORDER_SIZE) cnt++;
    return cnt >= 2;
}

static float minf(float a, float b) {
    return (a < b) ? a : b;
}

static char raytrace(vect pos, vect dir, const char* blocks, float* out_distance) {
    if (ray_outside(pos)) {
        *out_distance = MAX_DISTANCE;
        return ' ';
    }

    if (dir.x == 0.0f && dir.y == 0.0f && dir.z == 0.0f) {
        *out_distance = MAX_DISTANCE;
        return ' ';
    }

    int xi = (int)floorf(pos.x);
    int yi = (int)floorf(pos.y);
    int zi = (int)floorf(pos.z);

    if (xi < 0 || yi < 0 || zi < 0 || xi >= X_BLOCKS || yi >= Y_BLOCKS || zi >= Z_BLOCKS) {
        *out_distance = MAX_DISTANCE;
        return ' ';
    }

    char c0 = block_get(blocks, xi, yi, zi);
    if (c0 != ' ') {
        *out_distance = 0.0f;
        if (on_block_border(pos)) return '-';
        return c0;
    }

    if (dir.z > 0.99f && fabsf(dir.x) < 1e-3f && fabsf(dir.y) < 1e-3f) {
        int zi_step = zi + 1;
        const float inv_z = 1.0f / fmaxf(dir.z, 1e-6f);
        float distance = ((float)zi_step - pos.z) * inv_z;
        while (distance < MAX_DISTANCE && zi_step < Z_BLOCKS) {
            char c = block_get(blocks, xi, yi, zi_step);
            if (c != ' ') {
                *out_distance = distance;
                vect hit_pos = vect_add(pos, vect_scale(distance, dir));
                if (on_block_border(hit_pos)) return '-';
                return c;
            }
            zi_step += 1;
            distance = ((float)zi_step - pos.z) * inv_z;
        }
        *out_distance = MAX_DISTANCE;
        return ' ';
    }

    int step_x = 0, step_y = 0, step_z = 0;
    float tMaxX = FLT_MAX, tMaxY = FLT_MAX, tMaxZ = FLT_MAX;
    float tDeltaX = FLT_MAX, tDeltaY = FLT_MAX, tDeltaZ = FLT_MAX;

    if (dir.x > 0.0f) {
        step_x = 1;
        float offset = ((float)xi + 1.0f) - pos.x;
        tMaxX = offset / dir.x;
        tDeltaX = 1.0f / dir.x;
    } else if (dir.x < 0.0f) {
        step_x = -1;
        float offset = pos.x - (float)xi;
        tMaxX = offset / -dir.x;
        tDeltaX = 1.0f / -dir.x;
    }

    if (dir.y > 0.0f) {
        step_y = 1;
        float offset = ((float)yi + 1.0f) - pos.y;
        tMaxY = offset / dir.y;
        tDeltaY = 1.0f / dir.y;
    } else if (dir.y < 0.0f) {
        step_y = -1;
        float offset = pos.y - (float)yi;
        tMaxY = offset / -dir.y;
        tDeltaY = 1.0f / -dir.y;
    }

    if (dir.z > 0.0f) {
        step_z = 1;
        float offset = ((float)zi + 1.0f) - pos.z;
        tMaxZ = offset / dir.z;
        tDeltaZ = 1.0f / dir.z;
    } else if (dir.z < 0.0f) {
        step_z = -1;
        float offset = pos.z - (float)zi;
        tMaxZ = offset / -dir.z;
        tDeltaZ = 1.0f / -dir.z;
    }

    float distance = 0.0f;

    while (distance < MAX_DISTANCE) {
        if (tMaxX < tMaxY) {
            if (tMaxX < tMaxZ) {
                distance = tMaxX;
                tMaxX += tDeltaX;
                xi += step_x;
            } else {
                distance = tMaxZ;
                tMaxZ += tDeltaZ;
                zi += step_z;
            }
        } else {
            if (tMaxY < tMaxZ) {
                distance = tMaxY;
                tMaxY += tDeltaY;
                yi += step_y;
            } else {
                distance = tMaxZ;
                tMaxZ += tDeltaZ;
                zi += step_z;
            }
        }

        if (xi < 0 || yi < 0 || zi < 0 || xi >= X_BLOCKS || yi >= Y_BLOCKS || zi >= Z_BLOCKS) {
            *out_distance = MAX_DISTANCE;
            return ' ';
        }

        if (distance > MAX_DISTANCE) break;

        char c = block_get(blocks, xi, yi, zi);
        if (c != ' ') {
            *out_distance = distance;
            vect hit_pos = vect_add(pos, vect_scale(distance, dir));
            if (on_block_border(hit_pos)) return '-';
            return c;
        }
    }

    *out_distance = MAX_DISTANCE;
    return ' ';
}

static void get_picture(char** picture, float** depth, player_pos_view posview, const char* blocks) {
    vect2 tmp_view = posview.view;
    tmp_view.psi -= VIEW_HEIGHT / 2.0f;
    vect screen_down = angles_to_vect(tmp_view);
    tmp_view.psi += VIEW_HEIGHT;
    vect screen_up = angles_to_vect(tmp_view);
    tmp_view.psi -= VIEW_HEIGHT / 2.0f;
    tmp_view.phi -= VIEW_WIDTH / 2.0f;
    vect screen_left = angles_to_vect(tmp_view);
    tmp_view.phi += VIEW_WIDTH;
    vect screen_right = angles_to_vect(tmp_view);
    tmp_view.phi -= VIEW_WIDTH / 2.0f;

    vect screen_mid_vert = vect_scale(0.5f, vect_add(screen_up, screen_down));
    vect screen_mid_hor = vect_scale(0.5f, vect_add(screen_left, screen_right));
    vect mid_to_left = vect_sub(screen_left, screen_mid_hor);
    vect mid_to_up = vect_sub(screen_up, screen_mid_vert);

    const float inv_x = (X_PIXELS > 1) ? (2.0f / (float)(X_PIXELS - 1)) : 0.0f;
    const float inv_y = (Y_PIXELS > 1) ? (2.0f / (float)(Y_PIXELS - 1)) : 0.0f;
    vect step_x = vect_scale(inv_x, mid_to_left);
    vect step_y = vect_scale(inv_y, mid_to_up);

    vect row_base = vect_add(screen_mid_hor, mid_to_left);
    row_base = vect_add(row_base, mid_to_up);

    for (int y = 0; y < Y_PIXELS; ++y) {
        vect pixel_vec = row_base;
        for (int x = 0; x < X_PIXELS; ++x) {
            vect dir = pixel_vec;
            vect_normalize(&dir);

            float dist = MAX_DISTANCE;
            char c = raytrace(posview.pos, dir, blocks, &dist);
            picture[y][x] = c;
            depth[y][x] = dist;

            pixel_vec = vect_sub(pixel_vec, step_x);
        }
        row_base = vect_sub(row_base, step_y);
    }
}

static void draw_ascii(char** picture, float** depth) {
    ensure_frame_buffer();

    for (int y = 0; y < Y_PIXELS; ++y) {
        for (int x = 0; x < X_PIXELS; ++x) {
            int idx = y * X_PIXELS + x;
            char c = picture[y][x];
            float d = depth[y][x];

            frame_buffer[idx].Char.AsciiChar = (c == ' ') ? ' ' : c;
            WORD attr = 0;

            if (c == 'o') {
                attr = FOREGROUND_GREEN | FOREGROUND_INTENSITY;
            } else if (c == '-') {
                attr = FOREGROUND_BLUE | FOREGROUND_GREEN | FOREGROUND_INTENSITY;
            } else {
                WORD base = 0;
                switch (c) {
                case '~':
                    base = FOREGROUND_BLUE;
                    break;
                case '=':
                    base = FOREGROUND_GREEN;
                    break;
                case '#':
                    base = FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE;
                    break;
                case '|':
                    base = FOREGROUND_RED | FOREGROUND_GREEN;
                    break;
                case '&':
                    base = FOREGROUND_GREEN;
                    break;
                default:
                    base = FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE;
                    break;
                }

                if (d < 5.0f) {
                    attr = base | FOREGROUND_INTENSITY;
                } else if (d < 10.0f) {
                    attr = base;
                } else if (d < 15.0f) {
                    attr = FOREGROUND_INTENSITY;
                } else {
                    attr = 0;
                }
            }

            frame_buffer[idx].Attributes = attr;
        }
    }

    if (console_ready) {
        COORD home = { 0, 0 };
        SetConsoleCursorPosition(hStdout, home);
    }
    SMALL_RECT target = frame_rect;
    COORD origin = { 0, 0 };
    WriteConsoleOutputA(hStdout, frame_buffer, frame_size, origin, &target);
}

static vect get_current_block(player_pos_view posview, const char* blocks) {
    vect pos = posview.pos;
    vect dir = angles_to_vect(posview.view);
    const float eps = 0.01f;

    while (!ray_outside(pos)) {
        int xi = (int)floorf(pos.x);
        int yi = (int)floorf(pos.y);
        int zi = (int)floorf(pos.z);
        if (xi < 0 || yi < 0 || zi < 0 || xi >= X_BLOCKS || yi >= Y_BLOCKS || zi >= Z_BLOCKS) {
            break;
        }
        if (block_get(blocks, xi, yi, zi) != ' ') {
            return pos;
        }

        float dist = MAX_DISTANCE;

        if (dir.x > eps) {
            dist = minf(dist, (floorf(pos.x) + 1.0f - pos.x) / dir.x);
        } else if (dir.x < -eps) {
            dist = minf(dist, (pos.x - floorf(pos.x)) / -dir.x);
        }

        if (dir.y > eps) {
            dist = minf(dist, (floorf(pos.y) + 1.0f - pos.y) / dir.y);
        } else if (dir.y < -eps) {
            dist = minf(dist, (pos.y - floorf(pos.y)) / -dir.y);
        }

        if (dir.z > eps) {
            dist = minf(dist, (floorf(pos.z) + 1.0f - pos.z) / dir.z);
        } else if (dir.z < -eps) {
            dist = minf(dist, (pos.z - floorf(pos.z)) / -dir.z);
        }

        pos = vect_add(pos, vect_scale(dist + eps, dir));
    }
    return pos;
}

static void place_block(vect pos, char* blocks, char block) {
    int x = clamp_index((int)floorf(pos.x), X_BLOCKS);
    int y = clamp_index((int)floorf(pos.y), Y_BLOCKS);
    int z = clamp_index((int)floorf(pos.z), Z_BLOCKS);

    float dists[6];
    dists[0] = fabsf((float)x + 1.0f - pos.x);
    dists[1] = fabsf(pos.x - (float)x);
    dists[2] = fabsf((float)y + 1.0f - pos.y);
    dists[3] = fabsf(pos.y - (float)y);
    dists[4] = fabsf((float)z + 1.0f - pos.z);
    dists[5] = fabsf(pos.z - (float)z);

    int min_idx = 0;
    float min_dist = dists[0];
    for (int i = 1; i < 6; ++i) {
        if (dists[i] < min_dist) {
            min_dist = dists[i];
            min_idx = i;
        }
    }

    switch (min_idx) {
    case 0:
        if (x + 1 < X_BLOCKS) block_set(blocks, x + 1, y, z, block);
        break;
    case 1:
        if (x - 1 >= 0) block_set(blocks, x - 1, y, z, block);
        break;
    case 2:
        if (y + 1 < Y_BLOCKS) block_set(blocks, x, y + 1, z, block);
        break;
    case 3:
        if (y - 1 >= 0) block_set(blocks, x, y - 1, z, block);
        break;
    case 4:
        if (z + 1 < Z_BLOCKS) block_set(blocks, x, y, z + 1, block);
        break;
    case 5:
        if (z - 1 >= 0) block_set(blocks, x, y, z - 1, block);
        break;
    default:
        break;
    }
}

static void update_pos_view(player_pos_view* posview, const char* blocks, float dt) {
    float view_step = VIEW_SPEED * dt;
    float move_step = MOVE_SPEED * dt;

    if (is_key_pressed('w')) posview->view.psi += view_step;
    if (is_key_pressed('s')) posview->view.psi -= view_step;
    posview->view.psi = clampf(posview->view.psi, -1.2f, 1.2f);

    if (is_key_pressed('d')) posview->view.phi += view_step;
    if (is_key_pressed('a')) posview->view.phi -= view_step;

    vect forward = angles_to_vect(posview->view);
    vect forward_flat = { forward.x, forward.y, 0.0f };
    vect_normalize(&forward_flat);
    vect right = { forward_flat.y, -forward_flat.x, 0.0f };

    vect new_pos = posview->pos;

    if (is_key_pressed('i')) {
        new_pos = vect_add(new_pos, vect_scale(move_step, forward_flat));
    }
    if (is_key_pressed('k')) {
        new_pos = vect_sub(new_pos, vect_scale(move_step, forward_flat));
    }
    if (is_key_pressed('j')) {
        new_pos = vect_add(new_pos, vect_scale(move_step, right));
    }
    if (is_key_pressed('l')) {
        new_pos = vect_sub(new_pos, vect_scale(move_step, right));
    }

    new_pos.x = clampf(new_pos.x, 0.0f, (float)(X_BLOCKS - 0.001f));
    new_pos.y = clampf(new_pos.y, 0.0f, (float)(Y_BLOCKS - 0.001f));
    posview->pos.x = new_pos.x;
    posview->pos.y = new_pos.y;

    int x = clamp_index((int)floorf(posview->pos.x), X_BLOCKS);
    int y = clamp_index((int)floorf(posview->pos.y), Y_BLOCKS);

    int z_top = (int)floorf(posview->pos.z - EYE_HEIGHT + 0.01f);
    if (z_top >= 0 && z_top < Z_BLOCKS && block_get(blocks, x, y, z_top) != ' ') {
        posview->pos.z = (float)(z_top + 1) + EYE_HEIGHT;
    }

    int z_bottom = (int)floorf(posview->pos.z - EYE_HEIGHT - 0.01f);
    if (z_bottom >= 0 && z_bottom < Z_BLOCKS && block_get(blocks, x, y, z_bottom) == ' ') {
        posview->pos.z = (float)z_bottom + EYE_HEIGHT;
    }

    posview->pos.z = clampf(posview->pos.z, EYE_HEIGHT, (float)(Z_BLOCKS - 0.001f));
}

int main(void) {
    init_console();
    atexit(restore_console);

    char** picture = init_picture();
    float** depth = init_depth();
    char* blocks = init_blocks();
    player_pos_view posview = init_posview();

    world_seed = (unsigned int)time(NULL);
    generate_world(blocks, world_seed);

    DWORD prev_tick = GetTickCount();

    while (1) {
        DWORD current_tick = GetTickCount();
        float dt = (float)(current_tick - prev_tick) * 0.001f;
        if (dt < 0.0f) dt = 0.0f;
        if (dt > 0.1f) dt = 0.1f;
        prev_tick = current_tick;

        process_input();
        if (is_key_pressed('q')) {
            break;
        }

        update_pos_view(&posview, blocks, dt);

        vect current_block = get_current_block(posview, blocks);
        int have_block = !ray_outside(current_block);
        int block_x = clamp_index((int)floorf(current_block.x), X_BLOCKS);
        int block_y = clamp_index((int)floorf(current_block.y), Y_BLOCKS);
        int block_z = clamp_index((int)floorf(current_block.z), Z_BLOCKS);
        char saved_block = ' ';
        int removed = 0;

        DWORD now = current_tick;

        if (have_block) {
            saved_block = block_get(blocks, block_x, block_y, block_z);
            block_set(blocks, block_x, block_y, block_z, 'o');

            if (is_key_pressed('x') && now - last_break_tick >= ACTION_DELAY_MS) {
                block_set(blocks, block_x, block_y, block_z, ' ');
                removed = 1;
                last_break_tick = now;
            } else if (is_key_pressed(' ') && now - last_place_tick >= ACTION_DELAY_MS) {
                place_block(current_block, blocks, '@');
                last_place_tick = now;
            }
        }

        get_picture(picture, depth, posview, blocks);

        if (have_block && !removed) {
            block_set(blocks, block_x, block_y, block_z, saved_block);
        }

        draw_ascii(picture, depth);

        Sleep(FRAME_DELAY_MS);
    }

    restore_console();

    if (picture) {
        for (int y = 0; y < Y_PIXELS; ++y) free(picture[y]);
        free(picture);
    }
    if (depth) {
        for (int y = 0; y < Y_PIXELS; ++y) free(depth[y]);
        free(depth);
    }
    free_blocks(blocks);
    free(frame_buffer);

    return 0;
}
