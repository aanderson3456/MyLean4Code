// Lean compiler output
// Module: VTlean.Burnside
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_getLast___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_val(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_VTlean_List_moment(lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00LucasLehmer_sZMod_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Burnside_block__repeat_spec__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t lp_VTlean_Burnside_block__repeat___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Burnside_block__repeat___redArg___closed__0;
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_block__repeat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_block__repeat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_block__repeat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr___lam__0___boxed(lean_object*);
static const lean_closure_object lp_VTlean_Burnside_syndrome__slice__congr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_VTlean_Burnside_syndrome__slice__congr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_VTlean_Burnside_syndrome__slice__congr___closed__0 = (const lean_object*)&lp_VTlean_Burnside_syndrome__slice__congr___closed__0_value;
static lean_once_cell_t lp_VTlean_Burnside_syndrome__slice__congr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_VTlean_Burnside_syndrome__slice__congr___closed__1;
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_trans___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv__exists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv__exists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_List_getLast___redArg(x_2);
x_6 = lean_array_mk(x_2);
x_7 = lean_array_pop(x_6);
x_8 = lean_array_to_list(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_cyclicShift(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_cyclicShift(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_cyclicShift__k___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_cyclicShift(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShift__k___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_cyclicShift__k(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lp_VTlean_Burnside_cyclicShiftPow(x_1, x_7, x_3);
lean_dec(x_7);
x_9 = lp_VTlean_Burnside_cyclicShift(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_cyclicShiftPow(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lp_VTlean_Burnside_cyclicShiftPow__k___redArg(x_1, x_7, x_3);
lean_dec(x_7);
x_9 = lp_VTlean_Burnside_cyclicShift(x_1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_cyclicShiftPow__k___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Burnside_cyclicShiftPow__k___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_cyclicShiftPow__k___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Burnside_cyclicShiftPow__k(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lp_mathlib_ZMod_val(x_1, x_2);
x_5 = lp_VTlean_Burnside_cyclicShiftPow__k___redArg(x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_instAddActionZModWeight__subspaceOfNeZeroNat(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lp_VTlean_List_moment(x_2);
x_4 = lp_mathlib_Nat_cast___at___00LucasLehmer_sZMod_spec__0(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_moment__map___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_moment__map___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_moment__map___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_moment__map(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Burnside_block__repeat_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_List_foldl___at___00Array_appendList_spec__0___redArg(x_2, x_4);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_lp_VTlean_Burnside_block__repeat___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_block__repeat___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_List_replicateTR___redArg(x_2, x_1);
x_4 = lean_obj_once(&lp_VTlean_Burnside_block__repeat___redArg___closed__0, &lp_VTlean_Burnside_block__repeat___redArg___closed__0_once, _init_lp_VTlean_Burnside_block__repeat___redArg___closed__0);
x_5 = lp_VTlean___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Burnside_block__repeat_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_block__repeat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_block__repeat___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_block__repeat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_VTlean_Burnside_block__repeat(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_cyclicShift(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_shift__equiv___redArg___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_1, x_3);
x_5 = lp_VTlean_Burnside_cyclicShiftPow(x_1, x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_VTlean_Burnside_shift__equiv___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(lp_VTlean_Burnside_shift__equiv___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(lp_VTlean_Burnside_shift__equiv___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Burnside_shift__equiv___redArg(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Burnside_shift__equiv(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_VTlean_Burnside_syndrome__slice__congr___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_lp_VTlean_Burnside_syndrome__slice__congr___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(lp_VTlean_Burnside_syndrome__slice__congr___closed__0));
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_obj_once(&lp_VTlean_Burnside_syndrome__slice__congr___closed__1, &lp_VTlean_Burnside_syndrome__slice__congr___closed__1_once, _init_lp_VTlean_Burnside_syndrome__slice__congr___closed__1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_syndrome__slice__congr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_VTlean_Burnside_syndrome__slice__congr(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; 
x_7 = lp_VTlean_Burnside_syndrome__slice__congr(x_1, x_2, x_2, x_3, lean_box(0));
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_inc(x_1);
x_10 = lp_VTlean_Burnside_shift__equiv__pow___redArg(x_1, x_2, x_3, x_9);
x_11 = lean_nat_mul(x_9, x_3);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_11);
lean_inc(x_1);
x_13 = lp_VTlean_Burnside_shift__equiv___redArg(x_1);
x_14 = lp_mathlib_Equiv_trans___redArg(x_10, x_13);
x_15 = lean_nat_add(x_12, x_3);
lean_dec(x_12);
x_16 = lean_nat_add(x_9, x_8);
lean_dec(x_9);
x_17 = lean_nat_mul(x_16, x_3);
lean_dec(x_16);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_17);
x_19 = lp_VTlean_Burnside_syndrome__slice__congr(x_1, x_15, x_18, x_3, lean_box(0));
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_1);
x_20 = lp_mathlib_Equiv_trans___redArg(x_14, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Burnside_shift__equiv__pow___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_VTlean_Burnside_shift__equiv__pow___redArg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_shift__equiv__pow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_VTlean_Burnside_shift__equiv__pow(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv__exists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(0u);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv__exists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_VTlean_Burnside_coprime__syndrome__slice__equiv__exists(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_6 = lp_VTlean_Burnside_shift__equiv__pow___redArg(x_1, x_2, x_4, x_5);
x_7 = lp_VTlean_Burnside_syndrome__slice__congr(x_1, x_2, x_3, x_4, lean_box(0));
lean_dec(x_1);
x_8 = lp_mathlib_Equiv_trans___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_VTlean_Burnside_coprime__syndrome__slice__equiv___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_VTlean_Burnside_coprime__syndrome__slice__equiv___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_VTlean_Burnside_coprime__syndrome__slice__equiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lp_VTlean_Burnside_coprime__syndrome__slice__equiv(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_VTlean_VTlean_VTCode(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_VTlean_VTlean_Burnside(uint8_t builtin) {
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
