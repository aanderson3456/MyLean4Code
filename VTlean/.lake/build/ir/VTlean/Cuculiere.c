// Lean compiler output
// Module: VTlean.Cuculiere
// Imports: public import Init public import Mathlib public import VTlean.VTCode
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
static const lean_ctor_object lp_VTlean_pascal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_VTlean_pascal___closed__0 = (const lean_object*)&lp_VTlean_pascal___closed__0_value;
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_VTlean_pascal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_VTlean_pascal___closed__1 = (const lean_object*)&lp_VTlean_pascal___closed__1_value;
static const lean_ctor_object lp_VTlean_pascal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_VTlean_pascal___closed__2 = (const lean_object*)&lp_VTlean_pascal___closed__2_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t lp_VTlean_pascal___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_pascal___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_pascal(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_pascal___boxed(lean_object*);
lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_pascal__get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_pascal__get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_cuculiere(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_cuculiere___boxed(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_max__vt__checksum(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_max__vt__checksum___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_cuculiere__get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_cuculiere__get___boxed(lean_object*, lean_object*);
static lean_object* _init_lp_VTlean_pascal___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_pascal(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = ((lean_object*)(lp_VTlean_pascal___closed__0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = ((lean_object*)(lp_VTlean_pascal___closed__1));
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lp_VTlean_pascal(x_7);
lean_dec(x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = ((lean_object*)(lp_VTlean_pascal___closed__2));
x_11 = l_List_appendTR___redArg(x_8, x_10);
x_12 = lean_obj_once(&lp_VTlean_pascal___closed__3, &lp_VTlean_pascal___closed__3_once, _init_lp_VTlean_pascal___closed__3);
x_13 = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(x_5, x_11, x_9, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_pascal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_pascal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_pascal__get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_VTlean_pascal(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_getD___redArg(x_3, x_2, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_pascal__get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_pascal__get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean___private_VTlean_Cuculiere_0__pascal_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_cuculiere(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 1)
{
lean_object* x_4; 
x_4 = ((lean_object*)(lp_VTlean_pascal___closed__0));
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = ((lean_object*)(lp_VTlean_pascal___closed__1));
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lp_VTlean_cuculiere(x_7);
x_9 = lean_nat_add(x_7, x_6);
lean_dec(x_7);
x_10 = l_List_replicateTR___redArg(x_9, x_2);
lean_inc(x_8);
lean_inc(x_10);
x_11 = l_List_appendTR___redArg(x_10, x_8);
x_12 = l_List_appendTR___redArg(x_8, x_10);
x_13 = lean_obj_once(&lp_VTlean_pascal___closed__3, &lp_VTlean_pascal___closed__3_once, _init_lp_VTlean_pascal___closed__3);
x_14 = l___private_Init_Data_List_Impl_0__List_zipWithTR_go___redArg(x_5, x_12, x_11, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_cuculiere___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_cuculiere(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_max__vt__checksum(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_nat_mul(x_1, x_3);
lean_dec(x_3);
x_5 = lean_nat_shiftr(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_max__vt__checksum___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_max__vt__checksum(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_cuculiere__get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lp_VTlean_cuculiere(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_getD___redArg(x_3, x_2, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_cuculiere__get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_cuculiere__get(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Cuculiere(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_VTCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
