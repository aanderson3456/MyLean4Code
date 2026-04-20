// Lean compiler output
// Module: VTlean.VTCode
// Imports: public import Init public import VTlean.NumOsNumIs public import Mathlib
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_moment__sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_moment__sub___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_moment(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_moment___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_moment___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_moment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_moment___boxed(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_decidable__pred__VTCode___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_decidable__pred__VTCode___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_decidable__pred__VTCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_decidable__pred__VTCode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_moment__sub(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_2, x_7);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
x_13 = lp_VTlean_List_moment__sub(x_10, x_12);
x_14 = lean_nat_add(x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_moment__sub___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_List_moment__sub(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_moment(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lp_VTlean_List_moment__sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_moment___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_List_moment(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_moment___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(x_1);
x_3 = lp_VTlean_List_moment(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_moment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_moment___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_moment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_moment(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_VTlean_decidable__pred__VTCode___aux__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lp_VTlean_Vector_moment___redArg(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = lean_nat_mod(x_4, x_6);
lean_dec(x_4);
x_8 = lean_nat_mod(x_2, x_6);
lean_dec(x_6);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_VTlean_decidable__pred__VTCode___aux__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_decidable__pred__VTCode___aux__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_VTlean_decidable__pred__VTCode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_VTlean_decidable__pred__VTCode___aux__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_decidable__pred__VTCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_decidable__pred__VTCode(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_NumOsNumIs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_NumOsNumIs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
