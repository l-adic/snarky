// Lean compiler output
// Module: Pasta.Module
// Imports: public import Init public meta import Init public import Pasta.Basic
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
lean_object* lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_sw__add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_SWPoint_zero___redArg(lean_object*);
lean_object* lp_CompElliptic_CompElliptic_binNsmul___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_CompElliptic_CompElliptic_Curves_Pasta_Pallas_curve;
extern lean_object* lp_CompElliptic_CompElliptic_Fields_Pasta_instFieldFp;
extern lean_object* lp_CompElliptic_CompElliptic_Curves_Pasta_Vesta_curve;
extern lean_object* lp_CompElliptic_CompElliptic_Fields_Pasta_instFieldFq;
LEAN_EXPORT lean_object* lp_pasta_Pasta_vestaPointModule___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_pasta_Pasta_vestaPointModule___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t lp_pasta_Pasta_vestaPointModule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_pasta_Pasta_vestaPointModule___closed__0;
static lean_once_cell_t lp_pasta_Pasta_vestaPointModule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_pasta_Pasta_vestaPointModule___closed__1;
static lean_once_cell_t lp_pasta_Pasta_vestaPointModule___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_pasta_Pasta_vestaPointModule___closed__2;
LEAN_EXPORT lean_object* lp_pasta_Pasta_vestaPointModule;
static lean_once_cell_t lp_pasta_Pasta_pallasPointModule___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_pasta_Pasta_pallasPointModule___closed__0;
static lean_once_cell_t lp_pasta_Pasta_pallasPointModule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_pasta_Pasta_pallasPointModule___closed__1;
static lean_once_cell_t lp_pasta_Pasta_pallasPointModule___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_pasta_Pasta_pallasPointModule___closed__2;
LEAN_EXPORT lean_object* lp_pasta_Pasta_pallasPointModule;
LEAN_EXPORT lean_object* lp_pasta_Pasta_vestaPointModule___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_c_4_, lean_object* v_x_5_){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
lean_inc_ref(v___x_1_);
v___x_6_ = lean_alloc_closure((void*)(lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_sw__add), 6, 4);
lean_closure_set(v___x_6_, 0, lean_box(0));
lean_closure_set(v___x_6_, 1, v___x_1_);
lean_closure_set(v___x_6_, 2, v___x_2_);
lean_closure_set(v___x_6_, 3, v___x_3_);
v___x_7_ = lp_CompElliptic_CompElliptic_CurveForms_ShortWeierstrass_SWPoint_zero___redArg(v___x_1_);
lean_dec_ref(v___x_1_);
v___x_8_ = lp_CompElliptic_CompElliptic_binNsmul___redArg(v___x_6_, v___x_7_, v_c_4_, v_x_5_);
lean_dec_ref(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* lp_pasta_Pasta_vestaPointModule___lam__0___boxed(lean_object* v___x_9_, lean_object* v___x_10_, lean_object* v___x_11_, lean_object* v_c_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = lp_pasta_Pasta_vestaPointModule___lam__0(v___x_9_, v___x_10_, v___x_11_, v_c_12_, v_x_13_);
lean_dec(v_c_12_);
return v_res_14_;
}
}
static lean_object* _init_lp_pasta_Pasta_vestaPointModule___closed__0(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_cstr_to_nat("28948022309329048855892746252171976963363056481941647379679742748393362948097");
return v___x_15_;
}
}
static lean_object* _init_lp_pasta_Pasta_vestaPointModule___closed__1(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&lp_pasta_Pasta_vestaPointModule___closed__0, &lp_pasta_Pasta_vestaPointModule___closed__0_once, _init_lp_pasta_Pasta_vestaPointModule___closed__0);
v___x_17_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_lp_pasta_Pasta_vestaPointModule___closed__2(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___f_21_; 
v___x_18_ = lp_CompElliptic_CompElliptic_Curves_Pasta_Vesta_curve;
v___x_19_ = lean_obj_once(&lp_pasta_Pasta_vestaPointModule___closed__1, &lp_pasta_Pasta_vestaPointModule___closed__1_once, _init_lp_pasta_Pasta_vestaPointModule___closed__1);
v___x_20_ = lp_CompElliptic_CompElliptic_Fields_Pasta_instFieldFq;
v___f_21_ = lean_alloc_closure((void*)(lp_pasta_Pasta_vestaPointModule___lam__0___boxed), 5, 3);
lean_closure_set(v___f_21_, 0, v___x_20_);
lean_closure_set(v___f_21_, 1, v___x_19_);
lean_closure_set(v___f_21_, 2, v___x_18_);
return v___f_21_;
}
}
static lean_object* _init_lp_pasta_Pasta_vestaPointModule(void){
_start:
{
lean_object* v___f_22_; 
v___f_22_ = lean_obj_once(&lp_pasta_Pasta_vestaPointModule___closed__2, &lp_pasta_Pasta_vestaPointModule___closed__2_once, _init_lp_pasta_Pasta_vestaPointModule___closed__2);
return v___f_22_;
}
}
static lean_object* _init_lp_pasta_Pasta_pallasPointModule___closed__0(void){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_cstr_to_nat("28948022309329048855892746252171976963363056481941560715954676764349967630337");
return v___x_23_;
}
}
static lean_object* _init_lp_pasta_Pasta_pallasPointModule___closed__1(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_obj_once(&lp_pasta_Pasta_pallasPointModule___closed__0, &lp_pasta_Pasta_pallasPointModule___closed__0_once, _init_lp_pasta_Pasta_pallasPointModule___closed__0);
v___x_25_ = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_lp_pasta_Pasta_pallasPointModule___closed__2(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___f_29_; 
v___x_26_ = lp_CompElliptic_CompElliptic_Curves_Pasta_Pallas_curve;
v___x_27_ = lean_obj_once(&lp_pasta_Pasta_pallasPointModule___closed__1, &lp_pasta_Pasta_pallasPointModule___closed__1_once, _init_lp_pasta_Pasta_pallasPointModule___closed__1);
v___x_28_ = lp_CompElliptic_CompElliptic_Fields_Pasta_instFieldFp;
v___f_29_ = lean_alloc_closure((void*)(lp_pasta_Pasta_vestaPointModule___lam__0___boxed), 5, 3);
lean_closure_set(v___f_29_, 0, v___x_28_);
lean_closure_set(v___f_29_, 1, v___x_27_);
lean_closure_set(v___f_29_, 2, v___x_26_);
return v___f_29_;
}
}
static lean_object* _init_lp_pasta_Pasta_pallasPointModule(void){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = lean_obj_once(&lp_pasta_Pasta_pallasPointModule___closed__2, &lp_pasta_Pasta_pallasPointModule___closed__2_once, _init_lp_pasta_Pasta_pallasPointModule___closed__2);
return v___f_30_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_pasta_Pasta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_pasta_Pasta_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_pasta_Pasta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_pasta_Pasta_vestaPointModule = _init_lp_pasta_Pasta_vestaPointModule();
lean_mark_persistent(lp_pasta_Pasta_vestaPointModule);
lp_pasta_Pasta_pallasPointModule = _init_lp_pasta_Pasta_pallasPointModule();
lean_mark_persistent(lp_pasta_Pasta_pallasPointModule);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
