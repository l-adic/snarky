// Lean compiler output
// Module: Pasta.Basic
// Imports: public import Init public meta import Init public import Pasta.Curve public import Pasta.Constants public import CompElliptic.Curves.Pasta public import CompElliptic.Curves.PastaOrder public import CompElliptic.Fields.Pasta
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
LEAN_EXPORT lean_object* lp_pasta_Pasta_pastaFieldBits;
static lean_object* _init_lp_pasta_Pasta_pastaFieldBits(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(255u);
return v___x_1_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_pasta_Pasta_Curve(uint8_t builtin);
lean_object* initialize_pasta_Pasta_Constants(uint8_t builtin);
lean_object* initialize_CompElliptic_CompElliptic_Curves_Pasta(uint8_t builtin);
lean_object* initialize_CompElliptic_CompElliptic_Curves_PastaOrder(uint8_t builtin);
lean_object* initialize_CompElliptic_CompElliptic_Fields_Pasta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_pasta_Pasta_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_pasta_Pasta_Curve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_pasta_Pasta_Constants(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CompElliptic_CompElliptic_Curves_Pasta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CompElliptic_CompElliptic_Curves_PastaOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CompElliptic_CompElliptic_Fields_Pasta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_pasta_Pasta_pastaFieldBits = _init_lp_pasta_Pasta_pastaFieldBits();
lean_mark_persistent(lp_pasta_Pasta_pastaFieldBits);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
