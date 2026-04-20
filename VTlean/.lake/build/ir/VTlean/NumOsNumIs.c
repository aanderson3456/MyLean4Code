// Lean compiler output
// Module: VTlean.NumOsNumIs
// Imports: public import Init public import VTlean.B
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
LEAN_EXPORT lean_object* lp_VTlean_List_num__Is(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Is___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Os(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Os___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Is___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Is(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Is___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Os___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Os(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Os___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Is(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lp_VTlean_List_num__Is(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_num__Is___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_List_num__Is(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_num__Os(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unbox(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lp_VTlean_List_num__Os(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_6, x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_num__Os___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_List_num__Os(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Is___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(x_1);
x_3 = lp_VTlean_List_num__Is(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Is(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_num__Is___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Is___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_num__Is(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Os___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_array_to_list(x_1);
x_3 = lp_VTlean_List_num__Os(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Os(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_num__Os___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__Os___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_num__Os(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_B(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_NumOsNumIs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_B(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
