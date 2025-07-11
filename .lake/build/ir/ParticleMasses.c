// Lean compiler output
// Module: ParticleMasses
// Imports: Init Mathlib.Data.Real.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Tactic
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
extern lean_object* l___private_Mathlib_Data_Real_Basic_0__Real_zero;
static lean_object* l_RecognitionScience_particle__rungs___closed__3;
LEAN_EXPORT lean_object* l_RecognitionScience_particle__rungs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_RecognitionScience_particle__rungs(lean_object*);
static lean_object* l_RecognitionScience_particle__rungs___closed__2;
LEAN_EXPORT lean_object* l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_ofScientific(lean_object*, uint8_t, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_RecognitionScience_experimental__masses___closed__6;
static lean_object* l_RecognitionScience_particle__rungs___closed__1;
LEAN_EXPORT lean_object* l_RecognitionScience_experimental__masses(lean_object*);
static lean_object* l_RecognitionScience_experimental__masses___closed__3;
static lean_object* l_RecognitionScience_particle__rungs___closed__6;
LEAN_EXPORT lean_object* l_RecognitionScience_experimental__masses___boxed(lean_object*);
static lean_object* l_RecognitionScience_experimental__masses___closed__5;
lean_object* l_NNRat_cast___at_Real_instNNRatCast___spec__1(lean_object*);
static lean_object* l_RecognitionScience_particle__rungs___closed__5;
LEAN_EXPORT lean_object* l_NNRat_cast___at_RecognitionScience_experimental__masses___spec__1(lean_object*);
static lean_object* l_RecognitionScience_particle__rungs___closed__4;
LEAN_EXPORT lean_object* l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_RecognitionScience_experimental__masses___closed__4;
LEAN_EXPORT lean_object* l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter(lean_object*);
static lean_object* l_RecognitionScience_experimental__masses___closed__2;
static lean_object* l_RecognitionScience_experimental__masses___closed__1;
static lean_object* _init_l_RecognitionScience_particle__rungs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("e-", 2);
return x_1;
}
}
static lean_object* _init_l_RecognitionScience_particle__rungs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mu-", 3);
return x_1;
}
}
static lean_object* _init_l_RecognitionScience_particle__rungs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tau-", 4);
return x_1;
}
}
static lean_object* _init_l_RecognitionScience_particle__rungs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("W", 1);
return x_1;
}
}
static lean_object* _init_l_RecognitionScience_particle__rungs___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Z", 1);
return x_1;
}
}
static lean_object* _init_l_RecognitionScience_particle__rungs___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("H", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_RecognitionScience_particle__rungs(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_RecognitionScience_particle__rungs___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_RecognitionScience_particle__rungs___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_RecognitionScience_particle__rungs___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_RecognitionScience_particle__rungs___closed__4;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_RecognitionScience_particle__rungs___closed__5;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_RecognitionScience_particle__rungs___closed__6;
x_13 = lean_string_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_unsigned_to_nat(0u);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_unsigned_to_nat(58u);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_unsigned_to_nat(48u);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(48u);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_unsigned_to_nat(44u);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_unsigned_to_nat(39u);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_unsigned_to_nat(32u);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_RecognitionScience_particle__rungs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RecognitionScience_particle__rungs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_NNRat_cast___at_RecognitionScience_experimental__masses___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_1);
return x_2;
}
}
static lean_object* _init_l_RecognitionScience_experimental__masses___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(12525u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_RecognitionScience_experimental__masses___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(911876u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_RecognitionScience_experimental__masses___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(80377u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_RecognitionScience_experimental__masses___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(177686u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(5u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_RecognitionScience_experimental__masses___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(105658375u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(9u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_RecognitionScience_experimental__masses___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(5109989u);
x_2 = 1;
x_3 = lean_unsigned_to_nat(10u);
x_4 = l_Rat_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_RecognitionScience_experimental__masses(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_RecognitionScience_particle__rungs___closed__1;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_RecognitionScience_particle__rungs___closed__2;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_RecognitionScience_particle__rungs___closed__3;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_RecognitionScience_particle__rungs___closed__4;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_RecognitionScience_particle__rungs___closed__5;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_RecognitionScience_particle__rungs___closed__6;
x_13 = lean_string_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l___private_Mathlib_Data_Real_Basic_0__Real_zero;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_RecognitionScience_experimental__masses___closed__1;
x_16 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_RecognitionScience_experimental__masses___closed__2;
x_18 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_RecognitionScience_experimental__masses___closed__3;
x_20 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_RecognitionScience_experimental__masses___closed__4;
x_22 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_RecognitionScience_experimental__masses___closed__5;
x_24 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_RecognitionScience_experimental__masses___closed__6;
x_26 = l_NNRat_cast___at_Real_instNNRatCast___spec__1(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_RecognitionScience_experimental__masses___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_RecognitionScience_experimental__masses(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_RecognitionScience_particle__rungs___closed__1;
x_10 = lean_string_dec_eq(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_RecognitionScience_particle__rungs___closed__2;
x_12 = lean_string_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_RecognitionScience_particle__rungs___closed__3;
x_14 = lean_string_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_RecognitionScience_particle__rungs___closed__4;
x_16 = lean_string_dec_eq(x_1, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_RecognitionScience_particle__rungs___closed__5;
x_18 = lean_string_dec_eq(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_RecognitionScience_particle__rungs___closed__6;
x_20 = lean_string_dec_eq(x_1, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_apply_7(x_8, x_1, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return x_21;
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_6);
return x_6;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_5);
return x_5;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_4);
return x_4;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_ParticleMasses_0__RecognitionScience_particle__rungs_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Real_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ParticleMasses(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Real_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_RecognitionScience_particle__rungs___closed__1 = _init_l_RecognitionScience_particle__rungs___closed__1();
lean_mark_persistent(l_RecognitionScience_particle__rungs___closed__1);
l_RecognitionScience_particle__rungs___closed__2 = _init_l_RecognitionScience_particle__rungs___closed__2();
lean_mark_persistent(l_RecognitionScience_particle__rungs___closed__2);
l_RecognitionScience_particle__rungs___closed__3 = _init_l_RecognitionScience_particle__rungs___closed__3();
lean_mark_persistent(l_RecognitionScience_particle__rungs___closed__3);
l_RecognitionScience_particle__rungs___closed__4 = _init_l_RecognitionScience_particle__rungs___closed__4();
lean_mark_persistent(l_RecognitionScience_particle__rungs___closed__4);
l_RecognitionScience_particle__rungs___closed__5 = _init_l_RecognitionScience_particle__rungs___closed__5();
lean_mark_persistent(l_RecognitionScience_particle__rungs___closed__5);
l_RecognitionScience_particle__rungs___closed__6 = _init_l_RecognitionScience_particle__rungs___closed__6();
lean_mark_persistent(l_RecognitionScience_particle__rungs___closed__6);
l_RecognitionScience_experimental__masses___closed__1 = _init_l_RecognitionScience_experimental__masses___closed__1();
lean_mark_persistent(l_RecognitionScience_experimental__masses___closed__1);
l_RecognitionScience_experimental__masses___closed__2 = _init_l_RecognitionScience_experimental__masses___closed__2();
lean_mark_persistent(l_RecognitionScience_experimental__masses___closed__2);
l_RecognitionScience_experimental__masses___closed__3 = _init_l_RecognitionScience_experimental__masses___closed__3();
lean_mark_persistent(l_RecognitionScience_experimental__masses___closed__3);
l_RecognitionScience_experimental__masses___closed__4 = _init_l_RecognitionScience_experimental__masses___closed__4();
lean_mark_persistent(l_RecognitionScience_experimental__masses___closed__4);
l_RecognitionScience_experimental__masses___closed__5 = _init_l_RecognitionScience_experimental__masses___closed__5();
lean_mark_persistent(l_RecognitionScience_experimental__masses___closed__5);
l_RecognitionScience_experimental__masses___closed__6 = _init_l_RecognitionScience_experimental__masses___closed__6();
lean_mark_persistent(l_RecognitionScience_experimental__masses___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
