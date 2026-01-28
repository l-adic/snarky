// Polynomial FFI module for IPA deferred verification
//
// This module provides opaque polynomial types and the b_poly_coefficients
// function needed for verifying the deferred sg commitment check.

use ark_ec::short_weierstrass::Affine;
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use napi::bindgen_prelude::*;
use napi_derive::napi;

use super::pasta::pallas::scalar_field::FieldExternal as PallasFieldExternal;
use super::pasta::types::{
    PallasConfig, PallasGroup, PallasScalarField, VestaConfig, VestaGroup, VestaScalarField,
};
use super::pasta::vesta::scalar_field::FieldExternal as VestaFieldExternal;

use super::kimchi::circuit::{PallasProverIndexExternal, VestaProverIndexExternal};

/// Opaque polynomial type holding coefficients.
/// Used to pass polynomial data between FFI calls without exposing internals.
pub struct Polynomial<F: Field> {
    pub coeffs: Vec<F>,
}

/// Pallas polynomial (coefficients in Fp = Vesta scalar field)
pub type PallasPolynomialExternal = External<Polynomial<VestaScalarField>>;

/// Vesta polynomial (coefficients in Fq = Pallas scalar field)
pub type VestaPolynomialExternal = External<Polynomial<PallasScalarField>>;

// Use the actual b_poly_coefficients from poly-commitment
use poly_commitment::commitment::b_poly_coefficients;

// ─── Pallas (Fp circuits, Vesta group) ─────────────────────────────────────────

/// Create b_poly_coefficients for Pallas field (Fp = Vesta scalar field).
/// Takes IPA challenges and returns an opaque Polynomial object.
#[napi]
pub fn pallas_b_poly_coefficients(
    challenges: Vec<&VestaFieldExternal>,
) -> PallasPolynomialExternal {
    let chals: Vec<VestaScalarField> = challenges.iter().map(|c| ***c).collect();
    let coeffs = b_poly_coefficients(&chals);
    External::new(Polynomial { coeffs })
}

/// Get the number of coefficients in a Pallas polynomial.
#[napi]
pub fn pallas_poly_length(poly: &PallasPolynomialExternal) -> u32 {
    poly.coeffs.len() as u32
}

/// Get the coefficients from a Pallas polynomial.
#[napi]
pub fn pallas_poly_get_coeffs(poly: &PallasPolynomialExternal) -> Vec<VestaFieldExternal> {
    poly.coeffs.iter().map(|c| External::new(*c)).collect()
}

/// Verify the deferred sg commitment check for a Vesta proof (Pallas/Fp circuits).
///
/// Checks that sg = MSM(SRS.g, poly.coeffs).
///
/// Arguments:
/// - prover_index: The Vesta prover index (contains SRS)
/// - sg_x, sg_y: Coordinates of the sg commitment (in Vesta base field = Fq)
/// - poly: The b_poly coefficients
///
/// Note: For Pallas circuits, we use Vesta curve. Vesta has base field Fq (= PallasScalarField).
#[napi]
pub fn pallas_verify_deferred_check(
    prover_index: &VestaProverIndexExternal,
    sg_x: &PallasFieldExternal,
    sg_y: &PallasFieldExternal,
    poly: &PallasPolynomialExternal,
) -> bool {
    let sg: Affine<VestaConfig> = Affine::new_unchecked(**sg_x, **sg_y);
    let coeffs = &poly.coeffs;
    let g = &prover_index.srs.g;

    if g.len() < coeffs.len() {
        return false;
    }

    // sg = MSM(g, coeffs) - matching SRS::verify logic
    let bases: Vec<VestaGroup> = g.iter().take(coeffs.len()).cloned().collect();
    let computed = <VestaGroup as AffineRepr>::Group::msm_unchecked(&bases, coeffs).into_affine();

    computed == sg
}

// ─── Vesta (Fq circuits, Pallas group) ─────────────────────────────────────────

/// Create b_poly_coefficients for Vesta field (Fq = Pallas scalar field).
/// Takes IPA challenges and returns an opaque Polynomial object.
#[napi]
pub fn vesta_b_poly_coefficients(challenges: Vec<&PallasFieldExternal>) -> VestaPolynomialExternal {
    let chals: Vec<PallasScalarField> = challenges.iter().map(|c| ***c).collect();
    let coeffs = b_poly_coefficients(&chals);
    External::new(Polynomial { coeffs })
}

/// Get the number of coefficients in a Vesta polynomial.
#[napi]
pub fn vesta_poly_length(poly: &VestaPolynomialExternal) -> u32 {
    poly.coeffs.len() as u32
}

/// Get the coefficients from a Vesta polynomial.
#[napi]
pub fn vesta_poly_get_coeffs(poly: &VestaPolynomialExternal) -> Vec<PallasFieldExternal> {
    poly.coeffs.iter().map(|c| External::new(*c)).collect()
}

/// Verify the deferred sg commitment check for a Pallas proof (Vesta/Fq circuits).
///
/// Checks that sg = MSM(SRS.g, poly.coeffs).
///
/// Arguments:
/// - prover_index: The Pallas prover index (contains SRS)
/// - sg_x, sg_y: Coordinates of the sg commitment (in Pallas base field = Fq)
/// - poly: The b_poly coefficients
///
/// Note: For Vesta circuits, we use Pallas curve. Pallas has base field Fq (= VestaScalarField).
#[napi]
pub fn vesta_verify_deferred_check(
    prover_index: &PallasProverIndexExternal,
    sg_x: &VestaFieldExternal,
    sg_y: &VestaFieldExternal,
    poly: &VestaPolynomialExternal,
) -> bool {
    let sg: Affine<PallasConfig> = Affine::new_unchecked(**sg_x, **sg_y);
    let coeffs = &poly.coeffs;
    let g = &prover_index.srs.g;

    if g.len() < coeffs.len() {
        return false;
    }

    // sg = MSM(g, coeffs) - no blinding commitment
    let bases: Vec<PallasGroup> = g.iter().take(coeffs.len()).cloned().collect();
    let computed = <PallasGroup as AffineRepr>::Group::msm_unchecked(&bases, coeffs).into_affine();

    computed == sg
}
