// Lean compiler output
// Module: VTlean.InsDel
// Imports: public import Init public import Mathlib.Data.Vector.Basic public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Fintype.Basic public import VTlean.Lemma
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static const lean_string_object lp_VTlean_Vector_sDel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "VTlean"};
static const lean_object* lp_VTlean_Vector_sDel___closed__0 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__0_value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_VTlean_Vector_sDel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 77, 242, 85, 91, 0, 21, 177)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__1 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__1_value;
static const lean_string_object lp_VTlean_Vector_sDel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "InsDel"};
static const lean_object* lp_VTlean_Vector_sDel___closed__2 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__2_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__1_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 142, 170, 2, 4, 251, 66, 79)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__3 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__3_value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__3_value),((lean_object*)(((size_t)(12) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(30, 126, 249, 81, 123, 243, 73, 64)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__4 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__4_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__4_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(175, 62, 232, 73, 147, 163, 143, 57)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__5 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__5_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__5_value),((lean_object*)(((size_t)(12) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(93, 117, 100, 126, 173, 52, 176, 235)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__6 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__6_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__6_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(226, 178, 110, 145, 202, 147, 83, 202)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__7 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__7_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__7_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(123, 217, 211, 44, 69, 232, 47, 80)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__8 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__8_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__8_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 148, 93, 177, 202, 172, 137, 5)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__9 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__9_value;
static const lean_string_object lp_VTlean_Vector_sDel___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_sorry"};
static const lean_object* lp_VTlean_Vector_sDel___closed__10 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__10_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__9_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__10_value),LEAN_SCALAR_PTR_LITERAL(221, 137, 169, 81, 142, 244, 3, 189)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__11 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__11_value;
static const lean_string_object lp_VTlean_Vector_sDel___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* lp_VTlean_Vector_sDel___closed__12 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__12_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__11_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__12_value),LEAN_SCALAR_PTR_LITERAL(192, 239, 79, 8, 179, 224, 101, 50)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__13 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__13_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__13_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 209, 219, 209, 3, 38, 150, 135)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__14 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__14_value;
static const lean_ctor_object lp_VTlean_Vector_sDel___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__14_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 247, 98, 210, 192, 172, 101, 118)}};
static const lean_object* lp_VTlean_Vector_sDel___closed__15 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__15_value;
static lean_once_cell_t lp_VTlean_Vector_sDel___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sDel___closed__16;
static const lean_string_object lp_VTlean_Vector_sDel___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* lp_VTlean_Vector_sDel___closed__17 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__17_value;
static lean_once_cell_t lp_VTlean_Vector_sDel___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sDel___closed__18;
static const lean_string_object lp_VTlean_Vector_sDel___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* lp_VTlean_Vector_sDel___closed__19 = (const lean_object*)&lp_VTlean_Vector_sDel___closed__19_value;
static lean_once_cell_t lp_VTlean_Vector_sDel___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sDel___closed__20;
static lean_once_cell_t lp_VTlean_Vector_sDel___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sDel___closed__21;
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT lean_object* lp_VTlean_Vector_sDel(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_sDel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__3_value),((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(197, 140, 195, 211, 63, 172, 202, 141)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__0 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__0_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__0_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(8, 203, 155, 128, 90, 38, 157, 51)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__1 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__1_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__1_value),((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(205, 207, 37, 243, 168, 49, 176, 92)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__2 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__2_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__2_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(18, 253, 218, 58, 55, 12, 65, 46)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__3 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__3_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(171, 28, 171, 144, 7, 220, 245, 35)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__4 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__4_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__4_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(156, 204, 85, 87, 145, 219, 118, 36)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__5 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__5_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__5_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 184, 231, 66, 228, 38, 76, 89)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__6 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__6_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__6_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__12_value),LEAN_SCALAR_PTR_LITERAL(208, 168, 23, 95, 203, 79, 241, 230)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__7 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__7_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__7_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 227, 80, 104, 211, 231, 56, 117)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__8 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__8_value;
static const lean_ctor_object lp_VTlean_Vector_sIns___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sIns___closed__8_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 165, 48, 145, 197, 58, 150, 239)}};
static const lean_object* lp_VTlean_Vector_sIns___closed__9 = (const lean_object*)&lp_VTlean_Vector_sIns___closed__9_value;
static lean_once_cell_t lp_VTlean_Vector_sIns___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sIns___closed__10;
static lean_once_cell_t lp_VTlean_Vector_sIns___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sIns___closed__11;
static lean_once_cell_t lp_VTlean_Vector_sIns___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sIns___closed__12;
static lean_once_cell_t lp_VTlean_Vector_sIns___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_sIns___closed__13;
LEAN_EXPORT lean_object* lp_VTlean_Vector_sIns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_sIns___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_VTlean_Vector_dS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__3_value),((lean_object*)(((size_t)(23) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(64, 215, 129, 169, 238, 74, 82, 49)}};
static const lean_object* lp_VTlean_Vector_dS___closed__0 = (const lean_object*)&lp_VTlean_Vector_dS___closed__0_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__0_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(113, 55, 153, 152, 176, 57, 112, 84)}};
static const lean_object* lp_VTlean_Vector_dS___closed__1 = (const lean_object*)&lp_VTlean_Vector_dS___closed__1_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__1_value),((lean_object*)(((size_t)(23) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(229, 17, 11, 133, 158, 237, 157, 142)}};
static const lean_object* lp_VTlean_Vector_dS___closed__2 = (const lean_object*)&lp_VTlean_Vector_dS___closed__2_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__2_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(10, 41, 45, 19, 189, 189, 124, 205)}};
static const lean_object* lp_VTlean_Vector_dS___closed__3 = (const lean_object*)&lp_VTlean_Vector_dS___closed__3_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(179, 210, 230, 141, 20, 74, 14, 58)}};
static const lean_object* lp_VTlean_Vector_dS___closed__4 = (const lean_object*)&lp_VTlean_Vector_dS___closed__4_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__4_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(68, 219, 79, 131, 239, 154, 246, 46)}};
static const lean_object* lp_VTlean_Vector_dS___closed__5 = (const lean_object*)&lp_VTlean_Vector_dS___closed__5_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__5_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__10_value),LEAN_SCALAR_PTR_LITERAL(85, 147, 183, 86, 237, 209, 79, 241)}};
static const lean_object* lp_VTlean_Vector_dS___closed__6 = (const lean_object*)&lp_VTlean_Vector_dS___closed__6_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__6_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__12_value),LEAN_SCALAR_PTR_LITERAL(232, 147, 33, 136, 16, 242, 83, 157)}};
static const lean_object* lp_VTlean_Vector_dS___closed__7 = (const lean_object*)&lp_VTlean_Vector_dS___closed__7_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__7_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 11, 34, 189, 234, 255, 14, 7)}};
static const lean_object* lp_VTlean_Vector_dS___closed__8 = (const lean_object*)&lp_VTlean_Vector_dS___closed__8_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__8_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(123, 134, 214, 181, 34, 196, 169, 126)}};
static const lean_object* lp_VTlean_Vector_dS___closed__9 = (const lean_object*)&lp_VTlean_Vector_dS___closed__9_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__9_value),((lean_object*)(((size_t)(448962514) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(97, 144, 157, 26, 212, 32, 173, 104)}};
static const lean_object* lp_VTlean_Vector_dS___closed__10 = (const lean_object*)&lp_VTlean_Vector_dS___closed__10_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__10_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__17_value),LEAN_SCALAR_PTR_LITERAL(226, 190, 71, 149, 154, 36, 242, 16)}};
static const lean_object* lp_VTlean_Vector_dS___closed__11 = (const lean_object*)&lp_VTlean_Vector_dS___closed__11_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__11_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__19_value),LEAN_SCALAR_PTR_LITERAL(238, 186, 149, 97, 16, 249, 66, 128)}};
static const lean_object* lp_VTlean_Vector_dS___closed__12 = (const lean_object*)&lp_VTlean_Vector_dS___closed__12_value;
static const lean_ctor_object lp_VTlean_Vector_dS___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_dS___closed__12_value),((lean_object*)(((size_t)(26) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(7, 107, 206, 120, 126, 9, 27, 118)}};
static const lean_object* lp_VTlean_Vector_dS___closed__13 = (const lean_object*)&lp_VTlean_Vector_dS___closed__13_value;
LEAN_EXPORT lean_object* lp_VTlean_Vector_dS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_dS___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_VTlean_Vector_IS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_sDel___closed__3_value),((lean_object*)(((size_t)(27) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 43, 110, 112, 91, 7, 247, 191)}};
static const lean_object* lp_VTlean_Vector_IS___closed__0 = (const lean_object*)&lp_VTlean_Vector_IS___closed__0_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__0_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(128, 49, 223, 47, 68, 179, 135, 64)}};
static const lean_object* lp_VTlean_Vector_IS___closed__1 = (const lean_object*)&lp_VTlean_Vector_IS___closed__1_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__1_value),((lean_object*)(((size_t)(27) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(141, 155, 114, 126, 95, 119, 141, 228)}};
static const lean_object* lp_VTlean_Vector_IS___closed__2 = (const lean_object*)&lp_VTlean_Vector_IS___closed__2_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__2_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(210, 219, 203, 110, 13, 13, 233, 142)}};
static const lean_object* lp_VTlean_Vector_IS___closed__3 = (const lean_object*)&lp_VTlean_Vector_IS___closed__3_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__3_value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(107, 194, 52, 211, 100, 42, 1, 169)}};
static const lean_object* lp_VTlean_Vector_IS___closed__4 = (const lean_object*)&lp_VTlean_Vector_IS___closed__4_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__4_value),((lean_object*)(((size_t)(7) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(92, 14, 175, 239, 65, 247, 202, 107)}};
static const lean_object* lp_VTlean_Vector_IS___closed__5 = (const lean_object*)&lp_VTlean_Vector_IS___closed__5_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__5_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__10_value),LEAN_SCALAR_PTR_LITERAL(77, 210, 43, 43, 170, 69, 146, 189)}};
static const lean_object* lp_VTlean_Vector_IS___closed__6 = (const lean_object*)&lp_VTlean_Vector_IS___closed__6_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__6_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__12_value),LEAN_SCALAR_PTR_LITERAL(144, 53, 97, 204, 172, 193, 167, 56)}};
static const lean_object* lp_VTlean_Vector_IS___closed__7 = (const lean_object*)&lp_VTlean_Vector_IS___closed__7_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__7_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 143, 134, 71, 224, 127, 101, 18)}};
static const lean_object* lp_VTlean_Vector_IS___closed__8 = (const lean_object*)&lp_VTlean_Vector_IS___closed__8_value;
static const lean_ctor_object lp_VTlean_Vector_IS___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_VTlean_Vector_IS___closed__8_value),((lean_object*)&lp_VTlean_Vector_sDel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(35, 167, 98, 111, 235, 35, 254, 121)}};
static const lean_object* lp_VTlean_Vector_IS___closed__9 = (const lean_object*)&lp_VTlean_Vector_IS___closed__9_value;
static lean_once_cell_t lp_VTlean_Vector_IS___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_IS___closed__10;
static lean_once_cell_t lp_VTlean_Vector_IS___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_IS___closed__11;
static lean_once_cell_t lp_VTlean_Vector_IS___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_IS___closed__12;
static lean_once_cell_t lp_VTlean_Vector_IS___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Vector_IS___closed__13;
LEAN_EXPORT lean_object* lp_VTlean_Vector_IS(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_IS___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_VTlean_Vector_sDel___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3326317103u);
x_2 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__15));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_sDel___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__17));
x_2 = lean_obj_once(&lp_VTlean_Vector_sDel___closed__16, &lp_VTlean_Vector_sDel___closed__16_once, _init_lp_VTlean_Vector_sDel___closed__16);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_sDel___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__19));
x_2 = lean_obj_once(&lp_VTlean_Vector_sDel___closed__18, &lp_VTlean_Vector_sDel___closed__18_once, _init_lp_VTlean_Vector_sDel___closed__18);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_sDel___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(21u);
x_2 = lean_obj_once(&lp_VTlean_Vector_sDel___closed__20, &lp_VTlean_Vector_sDel___closed__20_once, _init_lp_VTlean_Vector_sDel___closed__20);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_sDel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = 0;
x_6 = lean_obj_once(&lp_VTlean_Vector_sDel___closed__21, &lp_VTlean_Vector_sDel___closed__21_once, _init_lp_VTlean_Vector_sDel___closed__21);
x_7 = lean_sorry(x_5);
x_8 = lean_apply_1(x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_sDel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Vector_sDel(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_lp_VTlean_Vector_sIns___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4114708301u);
x_2 = ((lean_object*)(lp_VTlean_Vector_sIns___closed__9));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_sIns___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__17));
x_2 = lean_obj_once(&lp_VTlean_Vector_sIns___closed__10, &lp_VTlean_Vector_sIns___closed__10_once, _init_lp_VTlean_Vector_sIns___closed__10);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_sIns___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__19));
x_2 = lean_obj_once(&lp_VTlean_Vector_sIns___closed__11, &lp_VTlean_Vector_sIns___closed__11_once, _init_lp_VTlean_Vector_sIns___closed__11);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_sIns___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(22u);
x_2 = lean_obj_once(&lp_VTlean_Vector_sIns___closed__12, &lp_VTlean_Vector_sIns___closed__12_once, _init_lp_VTlean_Vector_sIns___closed__12);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_sIns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 0;
x_7 = lean_obj_once(&lp_VTlean_Vector_sIns___closed__13, &lp_VTlean_Vector_sIns___closed__13_once, _init_lp_VTlean_Vector_sIns___closed__13);
x_8 = lean_sorry(x_6);
x_9 = lean_apply_1(x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_sIns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_VTlean_Vector_sIns(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_dS(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 0;
x_5 = ((lean_object*)(lp_VTlean_Vector_dS___closed__13));
x_6 = lean_sorry(x_4);
x_7 = lean_apply_1(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_dS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Vector_dS(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_lp_VTlean_Vector_IS___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3213995598u);
x_2 = ((lean_object*)(lp_VTlean_Vector_IS___closed__9));
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_IS___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__17));
x_2 = lean_obj_once(&lp_VTlean_Vector_IS___closed__10, &lp_VTlean_Vector_IS___closed__10_once, _init_lp_VTlean_Vector_IS___closed__10);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_IS___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(lp_VTlean_Vector_sDel___closed__19));
x_2 = lean_obj_once(&lp_VTlean_Vector_IS___closed__11, &lp_VTlean_Vector_IS___closed__11_once, _init_lp_VTlean_Vector_IS___closed__11);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_Vector_IS___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(26u);
x_2 = lean_obj_once(&lp_VTlean_Vector_IS___closed__12, &lp_VTlean_Vector_IS___closed__12_once, _init_lp_VTlean_Vector_IS___closed__12);
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_IS(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = 0;
x_5 = lean_obj_once(&lp_VTlean_Vector_IS___closed__13, &lp_VTlean_Vector_IS___closed__13_once, _init_lp_VTlean_Vector_IS___closed__13);
x_6 = lean_sorry(x_4);
x_7 = lean_apply_1(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_IS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Vector_IS(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Lemma(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_InsDel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Lemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
