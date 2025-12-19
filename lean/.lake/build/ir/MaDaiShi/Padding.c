// Lean compiler output
// Module: MaDaiShi.Padding
// Imports: Init MaDaiShi.Circuit MaDaiShi.SEquivalence MaDaiShi.ExtendedFrege
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
lean_object* lean_sorry(uint8_t);
LEAN_EXPORT lean_object* l_MaDaiShi_PadSingle(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__tilde___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_poly(lean_object*);
LEAN_EXPORT lean_object* l_MaDaiShi_PadSingle___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MaDaiShi_Pad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__log___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MaDaiShi_Pad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__log(lean_object*);
lean_object* lean_nat_log2(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__tilde(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_poly___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__log(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_nat_log2(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__log___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_MaDaiShi_Padding_0__MaDaiShi_O__log(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__tilde(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_nat_log2(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
lean_dec(x_2);
x_5 = lean_nat_mul(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_O__tilde___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_MaDaiShi_Padding_0__MaDaiShi_O__tilde(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_poly(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_mul(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_MaDaiShi_Padding_0__MaDaiShi_poly___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_MaDaiShi_Padding_0__MaDaiShi_poly(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_MaDaiShi_PadSingle(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = lean_sorry(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_MaDaiShi_PadSingle___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_MaDaiShi_PadSingle(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_MaDaiShi_Pad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = lean_sorry(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_MaDaiShi_Pad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_MaDaiShi_Pad(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_MaDaiShi_Circuit(uint8_t builtin, lean_object*);
lean_object* initialize_MaDaiShi_SEquivalence(uint8_t builtin, lean_object*);
lean_object* initialize_MaDaiShi_ExtendedFrege(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_MaDaiShi_Padding(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MaDaiShi_Circuit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MaDaiShi_SEquivalence(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_MaDaiShi_ExtendedFrege(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
