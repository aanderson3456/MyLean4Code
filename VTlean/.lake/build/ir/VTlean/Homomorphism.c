// Lean compiler output
// Module: VTlean.Homomorphism
// Imports: public import Init public import Mathlib public import VTlean.DelCode public import VTlean.VTCode public import VTlean.Optimal
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
LEAN_EXPORT lean_object* lp_VTlean_prefix__00___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_prefix__00(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_prefix__00___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_prefix__11___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_prefix__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_prefix__11___boxed(lean_object*, lean_object*);
lean_object* lp_VTlean_instDecidableEqB___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_lift__00___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_lift__00___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_VTlean_lift__00___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_VTlean_lift__00___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_VTlean_lift__00___closed__0 = (const lean_object*)&lp_VTlean_lift__00___closed__0_value;
lean_object* lp_mathlib_Finset_image___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_lift__00(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_lift__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_prefix__00___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_box(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_prefix__00(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_prefix__00___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_prefix__00___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_prefix__00(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_prefix__11___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_box(x_2);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_prefix__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_prefix__11___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_prefix__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_prefix__11(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_VTlean_lift__00___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(lp_VTlean_instDecidableEqB___boxed), 2, 0);
x_4 = l_instDecidableEqList___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_lift__00___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_VTlean_lift__00___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_lift__00(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(lp_VTlean_lift__00___closed__0));
x_4 = lean_alloc_closure((void*)(lp_VTlean_prefix__00___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lp_mathlib_Finset_image___redArg(x_3, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_lift__11(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = ((lean_object*)(lp_VTlean_lift__00___closed__0));
x_4 = lean_alloc_closure((void*)(lp_VTlean_prefix__11___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lp_mathlib_Finset_image___redArg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_DelCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_Optimal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Homomorphism(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_DelCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_VTCode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_VTlean_VTlean_Optimal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
