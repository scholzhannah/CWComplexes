// Lean compiler output
// Module: CWcomplexes.auxiliary
// Imports: Init Mathlib.Topology.IsLocalHomeomorph Mathlib.Topology.Homotopy.HomotopyGroup Mathlib.Topology.Sets.Compacts
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
LEAN_EXPORT lean_object* l_tokification___elambda__2___rarg(lean_object*);
LEAN_EXPORT lean_object* l_fromkification___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_tokification___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_fromkification___elambda__2___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_tokification___elambda__1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_tokification___elambda__2___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_tokification___elambda__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instkification___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fromkification___elambda__1___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_tokification___elambda__1(lean_object*);
LEAN_EXPORT lean_object* l_fromkification___elambda__2___rarg(lean_object*);
LEAN_EXPORT lean_object* l_instkification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_fromkification___elambda__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_fromkification___elambda__2(lean_object*);
LEAN_EXPORT lean_object* l_fromkification(lean_object*);
LEAN_EXPORT lean_object* l_tokification(lean_object*);
LEAN_EXPORT lean_object* l_instkification(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_instkification___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_instkification(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_tokification___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_tokification___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_tokification___elambda__1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_tokification___elambda__2___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_tokification___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_tokification___elambda__2___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_tokification(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_tokification___elambda__2___rarg___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_tokification___elambda__1___rarg___boxed), 1, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_tokification___elambda__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_tokification___elambda__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_tokification___elambda__2___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_tokification___elambda__2___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_fromkification___elambda__1___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_fromkification___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_fromkification___elambda__1___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_fromkification___elambda__2___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_fromkification___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_fromkification___elambda__2___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_fromkification(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_fromkification___elambda__2___rarg___boxed), 1, 0);
x_3 = lean_alloc_closure((void*)(l_fromkification___elambda__1___rarg___boxed), 1, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_fromkification___elambda__1___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_fromkification___elambda__1___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_fromkification___elambda__2___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_fromkification___elambda__2___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_IsLocalHomeomorph(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Homotopy_HomotopyGroup(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Topology_Sets_Compacts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CWcomplexes_auxiliary(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_IsLocalHomeomorph(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Homotopy_HomotopyGroup(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Topology_Sets_Compacts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
