import re

with open("cert_engine/cert_checker.c", "r") as f:
    code = f.read()

# 1. Add tags and globals
code = code.replace(
    "#define NODE_PAVING_WIN     0x04",
    "#define NODE_PAVING_WIN     0x04\n#define NODE_BREAKER_MOVE   0x05\n#define NODE_MAKER_BRANCH   0x06\n#define NODE_BREAKER_WIN    0x07"
)

code = code.replace(
    "static uint32_t g_current_depth = 0;",
    "static uint32_t g_current_depth = 0;\nstatic int g_breaker_mode = 0;\nstatic uint8_t g_W = 8;\nstatic uint8_t g_H = 8;"
)

# 2. Update validate_breaker_branch
bb_branch = """    if (offset + 3 > file_size) return -1;
    uint16_t num_children = *(uint16_t *)(base + offset + 1);
    int empty_cells = (g_W * g_H) - __builtin_popcountll(maker_bb | breaker_bb);
    if (num_children != empty_cells) return -5; // Universal quantification assertion
    size_t pos = offset + 3;"""
code = code.replace(
    "    if (offset + 3 > file_size) return -1;\n    uint16_t num_children = *(uint16_t *)(base + offset + 1);\n    size_t pos = offset + 3;",
    bb_branch
)

# 3. Add breaker functions
breaker_funcs = """static int validate_breaker_move(const uint8_t *base, size_t file_size,
                                 size_t offset,
                                 uint64_t maker_bb, uint64_t breaker_bb) {
    if (offset + 2 > file_size) return -1;
    uint8_t cell = base[offset + 1];
    uint64_t bit = cell_bit(cell);
    if ((maker_bb | breaker_bb) & bit) return -2; 
    g_maker_moves++; // Reusing counter for existential moves
    return validate_node(base, file_size, offset + 2, maker_bb, breaker_bb | bit);
}

static int validate_maker_branch(const uint8_t *base, size_t file_size,
                                 size_t offset,
                                 uint64_t maker_bb, uint64_t breaker_bb) {
    if (offset + 3 > file_size) return -1;
    uint16_t num_children = *(uint16_t *)(base + offset + 1);
    int empty_cells = (g_W * g_H) - __builtin_popcountll(maker_bb | breaker_bb);
    if (num_children != empty_cells) return -5; 
    size_t pos = offset + 3;
    if (pos + num_children * 5 > file_size) return -1;
    g_breaker_branches++; // Reusing counter for universal branches
    for (uint16_t i = 0; i < num_children; ++i) {
        uint8_t mcell = base[pos];
        uint32_t child_off = *(uint32_t *)(base + pos + 1);
        uint64_t bit = cell_bit(mcell);
        if ((maker_bb | breaker_bb) & bit) return -2;
        size_t child_abs = offset + child_off;
        int rc = validate_node(base, file_size, child_abs, maker_bb | bit, breaker_bb);
        if (rc != 0) return rc;
        pos += 5;
    }
    return 0;
}

static int validate_node(const uint8_t *base, size_t file_size,"""
code = code.replace("static int validate_node(const uint8_t *base, size_t file_size,", breaker_funcs)

# 4. Update validate_node
node_switch = """    if (g_breaker_mode && check_win(maker_bb)) return -6;

    uint8_t tag = base[offset];
    int res = 0;
    switch (tag) {
        case NODE_MAKER_MOVE:
            if (g_breaker_mode) return -4;
            res = validate_maker_move(base, file_size, offset, maker_bb, breaker_bb);
            break;
        case NODE_BREAKER_BRANCH:
            if (g_breaker_mode) return -4;
            res = validate_breaker_branch(base, file_size, offset, maker_bb, breaker_bb);
            break;
        case NODE_WIN:
        case NODE_PAVING_WIN:
            if (g_breaker_mode) return -4;
            g_win_nodes++;
            res = check_win(maker_bb) ? 0 : -3;
            break;
        case NODE_BREAKER_MOVE:
            if (!g_breaker_mode) return -4;
            res = validate_breaker_move(base, file_size, offset, maker_bb, breaker_bb);
            break;
        case NODE_MAKER_BRANCH:
            if (!g_breaker_mode) return -4;
            res = validate_maker_branch(base, file_size, offset, maker_bb, breaker_bb);
            break;
        case NODE_BREAKER_WIN:
            if (!g_breaker_mode) return -4;
            g_win_nodes++;
            if ((g_W * g_H) - __builtin_popcountll(maker_bb | breaker_bb) > 0) return -7;
            res = 0;
            break;"""

code = code.replace(
    "    uint8_t tag = base[offset];\n    int res = 0;\n    switch (tag) {\n        case NODE_MAKER_MOVE:\n            res = validate_maker_move(base, file_size, offset, maker_bb, breaker_bb);\n            break;\n        case NODE_BREAKER_BRANCH:\n            res = validate_breaker_branch(base, file_size, offset, maker_bb, breaker_bb);\n            break;\n        case NODE_WIN:\n        case NODE_PAVING_WIN:\n            g_win_nodes++;\n            // Base Case: The inductive proof terminates here. We verify S ⊆ M.\n            res = check_win(maker_bb) ? 0 : -3;\n            break;",
    node_switch
)

# 5. Update main CLI args and globals
code = code.replace(
    "        if (strcmp(argv[i], \"--json\") == 0) {\n            json_output = 1;\n        } else {\n            path = argv[i];\n        }",
    "        if (strcmp(argv[i], \"--json\") == 0) {\n            json_output = 1;\n        } else if (strcmp(argv[i], \"--breaker\") == 0) {\n            g_breaker_mode = 1;\n        } else {\n            path = argv[i];\n        }"
)

code = code.replace(
    "    uint8_t W = map[5];\n    uint8_t H = map[6];",
    "    uint8_t W = map[5];\n    uint8_t H = map[6];\n    g_W = W;\n    g_H = H;"
)

# 6. Output breaker mode string
code = code.replace(
    "Status          : %s\\n\", rc == 0 ? \"[SUCCESS] Certificate Validated\" : \"[FAIL] Invalid Certificate\");",
    "Status          : %s (%s Mode)\\n\", rc == 0 ? \"[SUCCESS] Certificate Validated\" : \"[FAIL] Invalid Certificate\", g_breaker_mode ? \"Breaker\" : \"Maker\");"
)

with open("cert_engine/cert_checker.c", "w") as f:
    f.write(code)

