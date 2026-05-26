// Lean compiler output
// Module: VTlean.Boolean
// Imports: public import Init public import Mathlib
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t lp_VTlean_deleteIdx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_deleteIdx___closed__0;
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_deleteIdx(lean_object*, lean_object*);
static lean_object* _init_lp_VTlean_deleteIdx___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_deleteIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_obj_once(&lp_VTlean_deleteIdx___closed__0, &lp_VTlean_deleteIdx___closed__0_once, _init_lp_VTlean_deleteIdx___closed__0);
lean_inc(x_2);
lean_inc(x_1);
x_4 = l___private_Init_Data_List_Impl_0__List_takeTR_go___redArg(x_1, x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_7 = l_List_drop___redArg(x_6, x_1);
lean_dec(x_1);
x_8 = l_List_appendTR___redArg(x_4, x_7);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Boolean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
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
