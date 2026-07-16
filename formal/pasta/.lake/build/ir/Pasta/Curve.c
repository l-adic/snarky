// Lean compiler output
// Module: Pasta.Curve
// Imports: public import Init public meta import Init public import Mathlib public import CompElliptic.CurveForms.ShortWeierstrass
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
lean_object* lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_toW___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___redArg(lean_object* v_inst_1_, lean_object* v_C_2_){
_start:
{
lean_object* v_A_3_; lean_object* v_B_4_; lean_object* v___x_5_; 
v_A_3_ = lean_ctor_get(v_C_2_, 0);
lean_inc(v_A_3_);
v_B_4_ = lean_ctor_get(v_C_2_, 1);
lean_inc(v_B_4_);
lean_dec_ref(v_C_2_);
v___x_5_ = lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_toW___redArg(v_inst_1_, v_A_3_, v_B_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___redArg___boxed(lean_object* v_inst_6_, lean_object* v_C_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___redArg(v_inst_6_, v_C_7_);
lean_dec_ref(v_inst_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine(lean_object* v_F_9_, lean_object* v_inst_10_, lean_object* v_C_11_){
_start:
{
lean_object* v_A_12_; lean_object* v_B_13_; lean_object* v___x_14_; 
v_A_12_ = lean_ctor_get(v_C_11_, 0);
lean_inc(v_A_12_);
v_B_13_ = lean_ctor_get(v_C_11_, 1);
lean_inc(v_B_13_);
lean_dec_ref(v_C_11_);
v___x_14_ = lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_toW___redArg(v_inst_10_, v_A_12_, v_B_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine___boxed(lean_object* v_F_15_, lean_object* v_inst_16_, lean_object* v_C_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = lp_pasta_CompElliptic_CurveForms_ShortWeierstrass_SWCurve_toAffine(v_F_15_, v_inst_16_, v_C_17_);
lean_dec_ref(v_inst_16_);
return v_res_18_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
lean_object* initialize_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_pasta_Pasta_Curve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
