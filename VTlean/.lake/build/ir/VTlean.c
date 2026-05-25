// Lean compiler output
// Module: VTlean
// Imports: public import Init public import VTlean.B public import VTlean.NumOsNumIs public import VTlean.VTCode public import VTlean.Lemma public import VTlean.InsDel public import VTlean.DelCode public import VTlean.Optimal public import VTlean.Homomorphism public import VTlean.Cuculiere public import VTlean.FractalSlice
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_B(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_NumOsNumIs(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Lemma(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_InsDel(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_DelCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Optimal(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Homomorphism(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Cuculiere(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_FractalSlice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_B(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_NumOsNumIs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_VTCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Lemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_InsDel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_DelCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Optimal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Homomorphism(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Cuculiere(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_FractalSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
