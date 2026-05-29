// Lean compiler output
// Module: VTlean.Networkx
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Fintype.Basic public import VTlean.B public import VTlean.InsDel public import VTlean.DelCode public import VTlean.VTCode public import VTlean.FractalSlice public import Mathlib.Tactic.ApplyFun
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
lean_object* lp_VTlean_instDecidableEqB___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___closed__0;
uint8_t lp_mathlib_Multiset_decidableMem___aux__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_VTlean_List_Vector_dS___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Finset_decidableDisjoint___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lp_mathlib_Fintype_decidableForallFintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object lp_VTlean_instDecidableIs__OptimalCodeCandidate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___closed__0 = (const lean_object*)&lp_VTlean_instDecidableIs__OptimalCodeCandidate___closed__0_value;
extern lean_object* lp_VTlean_B_enumList;
lean_object* lp_mathlib_Vector_fintype___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(lp_VTlean_instDecidableEqB___boxed), 2, 0);
x_4 = l_instDecidableEqList___redArg(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_instDecidableEqList___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(lp_VTlean_instDecidableEqB___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__1___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_6);
x_7 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_6, x_2);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_alloc_closure((void*)(lp_VTlean_instDecidableEqB___boxed), 2, 0);
lean_inc(x_6);
lean_inc(x_4);
lean_inc_ref(x_8);
x_9 = l_instDecidableEqList___redArg(x_8, x_4, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_obj_once(&lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___closed__0, &lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___closed__0_once, _init_lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___closed__0);
lean_inc_ref(x_8);
x_11 = lp_VTlean_List_Vector_dS___redArg(x_8, x_5, x_4);
x_12 = lp_VTlean_List_Vector_dS___redArg(x_8, x_5, x_6);
x_13 = lp_mathlib_Finset_decidableDisjoint___redArg(x_10, x_11, x_12);
return x_13;
}
else
{
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
x_8 = lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_2);
lean_inc(x_5);
lean_inc_ref(x_1);
x_6 = lp_mathlib_Multiset_decidableMem___aux__1___redArg(x_1, x_5, x_2);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(x_6);
x_9 = lean_alloc_closure((void*)(lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__2___boxed), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_3);
x_10 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_9, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__3(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t lp_VTlean_instDecidableIs__OptimalCodeCandidate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = ((lean_object*)(lp_VTlean_instDecidableIs__OptimalCodeCandidate___closed__0));
x_4 = lp_VTlean_B_enumList;
lean_inc(x_1);
x_5 = lp_mathlib_Vector_fintype___redArg(x_4, x_1);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(lp_VTlean_instDecidableIs__OptimalCodeCandidate___lam__3___boxed), 5, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_5);
x_7 = lp_mathlib_Fintype_decidableForallFintype___redArg(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_instDecidableIs__OptimalCodeCandidate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_VTlean_instDecidableIs__OptimalCodeCandidate(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean___private_VTlean_Networkx_0__cumulativeDels_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Basic(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_B(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_InsDel(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_DelCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_FractalSlice(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_ApplyFun(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Networkx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Basic(builtin);
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
res = initialize_mathlib_Mathlib_Tactic_ApplyFun(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
