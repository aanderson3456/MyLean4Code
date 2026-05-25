// Lean compiler output
// Module: VTlean.NumOsNumIs
// Imports: public import Init public import VTlean.B public import VTlean.InsDel public import Mathlib.Data.Finset.Basic
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
LEAN_EXPORT lean_object* lp_VTlean_List_num__Os(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Os___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Is(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__Is___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__LOs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__LOs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__RIs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_List_num__RIs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Iic__wt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Iic__wt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Iic__wt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Iic__wt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Icc__wt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Icc__wt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Icc__wt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Icc__wt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Ici__wt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Ici__wt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Ici__wt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Ici__wt___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lp_VTlean_List_num__LOs(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 1)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = lean_unbox(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lp_VTlean_List_num__LOs(x_5, x_9);
x_12 = lean_nat_add(x_11, x_8);
lean_dec(x_11);
return x_12;
}
else
{
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_num__LOs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_List_num__LOs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_num__RIs(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lp_VTlean_List_num__Is(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_List_num__RIs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_List_num__RIs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_List_num__Is(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_Vector_wt___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_List_num__Is(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_wt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_wt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_List_num__LOs(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_num__LOs___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_List_num__LOs(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__LOs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Vector_num__LOs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_List_num__RIs(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Vector_num__RIs___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_List_num__RIs(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_num__RIs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Vector_num__RIs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Iic__wt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lp_VTlean_List_num__Is(x_2);
x_4 = lean_nat_dec_le(x_3, x_1);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Iic__wt___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_VTlean_Vector_decidable__pred__Iic__wt___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Iic__wt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_VTlean_Vector_decidable__pred__Iic__wt___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Iic__wt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_Vector_decidable__pred__Iic__wt(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Icc__wt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lp_VTlean_List_num__Is(x_3);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_2);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Icc__wt___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_Vector_decidable__pred__Icc__wt___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Icc__wt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_VTlean_Vector_decidable__pred__Icc__wt___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Icc__wt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_VTlean_Vector_decidable__pred__Icc__wt(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Ici__wt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lp_VTlean_List_num__Is(x_2);
x_4 = lean_nat_dec_le(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Ici__wt___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_VTlean_Vector_decidable__pred__Ici__wt___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_VTlean_Vector_decidable__pred__Ici__wt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lp_VTlean_Vector_decidable__pred__Ici__wt___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Vector_decidable__pred__Ici__wt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_VTlean_Vector_decidable__pred__Ici__wt(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_B(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_InsDel(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Finset_Basic(uint8_t builtin);
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
res = initialize_VTlean_VTlean_InsDel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Finset_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
