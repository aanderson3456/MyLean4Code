// Lean compiler output
// Module: VTlean.Progressive
// Imports: public import Init public import VTlean.B public import VTlean.InsDel public import VTlean.DelCode public import VTlean.VTCode public import VTlean.FractalSlice public import VTlean.Networkx public import VTlean.Cuculiere
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
LEAN_EXPORT lean_object* lp_VTlean_P___lam__0(lean_object*, lean_object*);
lean_object* lp_VTlean_cumulativeDels(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_P(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_P___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_P___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_P(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(lp_VTlean_P___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = lp_VTlean_cumulativeDels(x_1, x_2, x_3);
x_7 = lp_mathlib_Finset_sum___at___00bernoulli_x27_spec__1___redArg(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_P___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_P(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_B(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_InsDel(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_DelCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_FractalSlice(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Networkx(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Cuculiere(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Progressive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_B(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_InsDel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_DelCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_VTCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_FractalSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Networkx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Cuculiere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
