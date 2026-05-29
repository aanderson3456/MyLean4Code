// Lean compiler output
// Module: VTlean.Dream
// Imports: public import Init public import Mathlib.Data.Finset.Basic public import Mathlib.Data.Fintype.Basic public import VTlean.B public import VTlean.InsDel public import VTlean.DelCode public import VTlean.VTCode public import VTlean.FractalSlice public import VTlean.Networkx
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
lean_object* lp_VTlean_List_Vector_dS___at___00List_Vector_union__dS___at___00B_dB_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_num__words__with__runs___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_num__words__with__runs___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_num__words__with__runs(lean_object*, lean_object*, lean_object*);
lean_object* lp_VTlean_instDecidableEqB___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_List_elem___at___00Multiset_ndinsert___at___00counterexample__C_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_elem___at___00Multiset_ndinsert___at___00counterexample__C_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(lean_object*, lean_object*);
static lean_once_cell_t lp_VTlean_counterexample__C___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__0;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__1;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__2;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__3;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__4;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__5;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__6;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__7;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__8;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__9;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__10;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__11;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__12;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__13;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__14;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__15;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__16;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__17;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__18;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__19;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__20;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__21;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__22;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__23;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__24;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__25;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__26;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__27;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__28;
static lean_once_cell_t lp_VTlean_counterexample__C___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_counterexample__C___closed__29;
LEAN_EXPORT lean_object* lp_VTlean_counterexample__C;
LEAN_EXPORT uint8_t lp_VTlean_num__words__with__runs___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lp_VTlean_List_Vector_dS___at___00List_Vector_union__dS___at___00B_dB_spec__0_spec__0(x_1, x_3);
x_5 = l_List_lengthTR___redArg(x_4);
lean_dec(x_4);
x_6 = lean_nat_dec_eq(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_num__words__with__runs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_num__words__with__runs___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_num__words__with__runs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(lp_VTlean_num__words__with__runs___lam__0___boxed), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_Multiset_filter___redArg(x_4, x_2);
x_6 = l_List_lengthTR___redArg(x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_VTlean_List_elem___at___00Multiset_ndinsert___at___00counterexample__C_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_alloc_closure((void*)(lp_VTlean_instDecidableEqB___boxed), 2, 0);
lean_inc(x_1);
x_7 = l_instDecidableEqList___redArg(x_6, x_1, x_4);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_elem___at___00Multiset_ndinsert___at___00counterexample__C_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_VTlean_List_elem___at___00Multiset_ndinsert___at___00counterexample__C_spec__0_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = lp_VTlean_List_elem___at___00Multiset_ndinsert___at___00counterexample__C_spec__0_spec__0(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__1(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__0, &lp_VTlean_counterexample__C___closed__0_once, _init_lp_VTlean_counterexample__C___closed__0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__2(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__1, &lp_VTlean_counterexample__C___closed__1_once, _init_lp_VTlean_counterexample__C___closed__1);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__3(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__2, &lp_VTlean_counterexample__C___closed__2_once, _init_lp_VTlean_counterexample__C___closed__2);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__4(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__3, &lp_VTlean_counterexample__C___closed__3_once, _init_lp_VTlean_counterexample__C___closed__3);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__5(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__6(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__5, &lp_VTlean_counterexample__C___closed__5_once, _init_lp_VTlean_counterexample__C___closed__5);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__7(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__6, &lp_VTlean_counterexample__C___closed__6_once, _init_lp_VTlean_counterexample__C___closed__6);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__8(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__7, &lp_VTlean_counterexample__C___closed__7_once, _init_lp_VTlean_counterexample__C___closed__7);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__9(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__8, &lp_VTlean_counterexample__C___closed__8_once, _init_lp_VTlean_counterexample__C___closed__8);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__10(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__5, &lp_VTlean_counterexample__C___closed__5_once, _init_lp_VTlean_counterexample__C___closed__5);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__11(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__10, &lp_VTlean_counterexample__C___closed__10_once, _init_lp_VTlean_counterexample__C___closed__10);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__12(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__11, &lp_VTlean_counterexample__C___closed__11_once, _init_lp_VTlean_counterexample__C___closed__11);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__13(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__12, &lp_VTlean_counterexample__C___closed__12_once, _init_lp_VTlean_counterexample__C___closed__12);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__14(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__0, &lp_VTlean_counterexample__C___closed__0_once, _init_lp_VTlean_counterexample__C___closed__0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__15(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__14, &lp_VTlean_counterexample__C___closed__14_once, _init_lp_VTlean_counterexample__C___closed__14);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__16(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__15, &lp_VTlean_counterexample__C___closed__15_once, _init_lp_VTlean_counterexample__C___closed__15);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__17(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__16, &lp_VTlean_counterexample__C___closed__16_once, _init_lp_VTlean_counterexample__C___closed__16);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__18(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__1, &lp_VTlean_counterexample__C___closed__1_once, _init_lp_VTlean_counterexample__C___closed__1);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__19(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__18, &lp_VTlean_counterexample__C___closed__18_once, _init_lp_VTlean_counterexample__C___closed__18);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__20(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__19, &lp_VTlean_counterexample__C___closed__19_once, _init_lp_VTlean_counterexample__C___closed__19);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__21(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__6, &lp_VTlean_counterexample__C___closed__6_once, _init_lp_VTlean_counterexample__C___closed__6);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__22(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__21, &lp_VTlean_counterexample__C___closed__21_once, _init_lp_VTlean_counterexample__C___closed__21);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__23(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__22, &lp_VTlean_counterexample__C___closed__22_once, _init_lp_VTlean_counterexample__C___closed__22);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&lp_VTlean_counterexample__C___closed__23, &lp_VTlean_counterexample__C___closed__23_once, _init_lp_VTlean_counterexample__C___closed__23);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__24, &lp_VTlean_counterexample__C___closed__24_once, _init_lp_VTlean_counterexample__C___closed__24);
x_2 = lean_obj_once(&lp_VTlean_counterexample__C___closed__20, &lp_VTlean_counterexample__C___closed__20_once, _init_lp_VTlean_counterexample__C___closed__20);
x_3 = lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__25, &lp_VTlean_counterexample__C___closed__25_once, _init_lp_VTlean_counterexample__C___closed__25);
x_2 = lean_obj_once(&lp_VTlean_counterexample__C___closed__17, &lp_VTlean_counterexample__C___closed__17_once, _init_lp_VTlean_counterexample__C___closed__17);
x_3 = lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__26, &lp_VTlean_counterexample__C___closed__26_once, _init_lp_VTlean_counterexample__C___closed__26);
x_2 = lean_obj_once(&lp_VTlean_counterexample__C___closed__13, &lp_VTlean_counterexample__C___closed__13_once, _init_lp_VTlean_counterexample__C___closed__13);
x_3 = lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__27, &lp_VTlean_counterexample__C___closed__27_once, _init_lp_VTlean_counterexample__C___closed__27);
x_2 = lean_obj_once(&lp_VTlean_counterexample__C___closed__9, &lp_VTlean_counterexample__C___closed__9_once, _init_lp_VTlean_counterexample__C___closed__9);
x_3 = lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_counterexample__C___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__28, &lp_VTlean_counterexample__C___closed__28_once, _init_lp_VTlean_counterexample__C___closed__28);
x_2 = lean_obj_once(&lp_VTlean_counterexample__C___closed__4, &lp_VTlean_counterexample__C___closed__4_once, _init_lp_VTlean_counterexample__C___closed__4);
x_3 = lp_VTlean_Multiset_ndinsert___at___00counterexample__C_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_lp_VTlean_counterexample__C(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_VTlean_counterexample__C___closed__29, &lp_VTlean_counterexample__C___closed__29_once, _init_lp_VTlean_counterexample__C___closed__29);
return x_1;
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
lean_object* initialize_VTlean_VTlean_Networkx(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Dream(uint8_t builtin) {
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
res = initialize_VTlean_VTlean_Networkx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_VTlean_counterexample__C = _init_lp_VTlean_counterexample__C();
lean_mark_persistent(lp_VTlean_counterexample__C);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
