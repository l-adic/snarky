// Linearization polynomial evaluation for testing against PureScript implementation
//
// This module provides FFI functions to evaluate Kimchi linearization polynomials
// so we can verify the PureScript interpreter produces identical results.
//
// ## Why we vendored the evaluate function
//
// Kimchi's `PolishToken::evaluate` function cannot be used directly because
// `FeatureFlag::is_enabled()` is implemented as `todo!("Handle features")`,
// causing a panic whenever the linearization contains SkipIf/SkipIfNot tokens.
//
// We copied the evaluation logic here with a fix: all feature flags are treated
// as disabled, which means:
// - SkipIf(feature, count): feature disabled → don't skip, evaluate normally
// - SkipIfNot(feature, count): feature disabled → skip count tokens, push zero
//
// This matches the OCaml implementation in mina/src/lib/pickles/plonk_checks/plonk_checks.ml
// where `if_feature` falls back to the "else" branch when a feature is None/disabled.
//
// TODO: Once upstream Kimchi implements FeatureFlag::is_enabled() properly,
// we can remove this vendored evaluate function and use PolishToken::evaluate directly.
// See: https://github.com/o1-labs/proof-systems/blob/main/kimchi/src/circuits/expr.rs

use ark_ff::{FftField, Field, Zero};
use ark_poly::{EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain};
use kimchi::circuits::berkeley_columns::{BerkeleyChallengeTerm, Column};
use kimchi::circuits::expr::{ColumnEvaluations, ConstantTerm, Constants, ExprError, PolishToken};
use kimchi::circuits::gate::CurrOrNext;
use kimchi::circuits::wires::COLUMNS;
use kimchi::linearization::{constraints_expr, linearization_columns};
use kimchi::proof::PointEvaluations;
use mina_curves::pasta::{Pallas, Vesta};
use mina_poseidon::pasta::{fp_kimchi, fq_kimchi};
use napi::bindgen_prelude::*;
use napi_derive::napi;
use poly_commitment::ipa::endos;
use std::collections::HashMap;
use std::ops::Index;

// Import field types with clear names
use crate::pasta::types::{PallasBaseField, VestaBaseField};
// External FFI types for field elements
use crate::pasta::pallas::scalar_field::FieldExternal as VestaBaseFieldExternal;
use crate::pasta::vesta::scalar_field::FieldExternal as PallasBaseFieldExternal;
// Import circuit gate types for coefficient/selector evaluation
use crate::kimchi::circuit::{PallasCircuitGateExternal, VestaCircuitGateExternal};

/// Number of witness columns
const WITNESS_COLS: usize = COLUMNS;

/// Number of coefficient columns - typically 15 for Kimchi
const COEFF_COLS: usize = 15;

/// Challenges container that implements Index<BerkeleyChallengeTerm>
struct Challenges<F: Field> {
    alpha: F,
    beta: F,
    gamma: F,
    joint_combiner: F,
}

impl<F: Field> Index<BerkeleyChallengeTerm> for Challenges<F> {
    type Output = F;

    fn index(&self, index: BerkeleyChallengeTerm) -> &Self::Output {
        match index {
            BerkeleyChallengeTerm::Alpha => &self.alpha,
            BerkeleyChallengeTerm::Beta => &self.beta,
            BerkeleyChallengeTerm::Gamma => &self.gamma,
            BerkeleyChallengeTerm::JointCombiner => &self.joint_combiner,
        }
    }
}

/// Column evaluations that implements the ColumnEvaluations trait
struct TestColumnEvaluations<F: Field> {
    /// Witness column evaluations [column][curr/next]
    witness: [[F; 2]; WITNESS_COLS],
    /// Coefficient evaluations (only at zeta, not zeta*omega)
    coefficients: [F; COEFF_COLS],
    /// Index/selector evaluations per gate type
    index: HashMap<kimchi::circuits::gate::GateType, [F; 2]>,
    /// Lookup aggregation
    lookup_aggregation: [F; 2],
    /// Lookup sorted
    lookup_sorted: [[F; 2]; 5],
    /// Lookup table
    lookup_table: [F; 2],
    /// Runtime lookup table
    runtime_lookup_table: [F; 2],
    /// Runtime lookup table selector
    runtime_lookup_table_selector: [F; 2],
    /// Lookup kind index (by pattern)
    lookup_kind_index: HashMap<kimchi::circuits::lookup::lookups::LookupPattern, F>,
}

impl<F: Field> TestColumnEvaluations<F> {
    fn new_zero() -> Self {
        Self {
            witness: [[F::zero(); 2]; WITNESS_COLS],
            coefficients: [F::zero(); COEFF_COLS],
            index: HashMap::new(),
            lookup_aggregation: [F::zero(); 2],
            lookup_sorted: [[F::zero(); 2]; 5],
            lookup_table: [F::zero(); 2],
            runtime_lookup_table: [F::zero(); 2],
            runtime_lookup_table_selector: [F::zero(); 2],
            lookup_kind_index: HashMap::new(),
        }
    }
}

impl<F: Field + Copy> kimchi::circuits::expr::ColumnEvaluations<F> for TestColumnEvaluations<F> {
    type Column = Column;

    fn evaluate(
        &self,
        col: Self::Column,
    ) -> std::result::Result<PointEvaluations<F>, kimchi::circuits::expr::ExprError<Self::Column>>
    {
        match col {
            Column::Witness(i) => Ok(PointEvaluations {
                zeta: self.witness[i][0],
                zeta_omega: self.witness[i][1],
            }),
            Column::Coefficient(i) => Ok(PointEvaluations {
                zeta: self.coefficients[i],
                zeta_omega: F::zero(), // coefficients don't have zeta_omega
            }),
            Column::Index(gate_type) => {
                let default = [F::zero(), F::zero()];
                let evals = self.index.get(&gate_type).unwrap_or(&default);
                Ok(PointEvaluations {
                    zeta: evals[0],
                    zeta_omega: evals[1],
                })
            }
            Column::LookupAggreg => Ok(PointEvaluations {
                zeta: self.lookup_aggregation[0],
                zeta_omega: self.lookup_aggregation[1],
            }),
            Column::LookupSorted(i) => Ok(PointEvaluations {
                zeta: self.lookup_sorted[i][0],
                zeta_omega: self.lookup_sorted[i][1],
            }),
            Column::LookupTable => Ok(PointEvaluations {
                zeta: self.lookup_table[0],
                zeta_omega: self.lookup_table[1],
            }),
            Column::LookupRuntimeTable => Ok(PointEvaluations {
                zeta: self.runtime_lookup_table[0],
                zeta_omega: self.runtime_lookup_table[1],
            }),
            Column::LookupRuntimeSelector => Ok(PointEvaluations {
                zeta: self.runtime_lookup_table_selector[0],
                zeta_omega: self.runtime_lookup_table_selector[1],
            }),
            Column::LookupKindIndex(pattern) => {
                let val = self
                    .lookup_kind_index
                    .get(&pattern)
                    .copied()
                    .unwrap_or(F::zero());
                Ok(PointEvaluations {
                    zeta: val,
                    zeta_omega: F::zero(),
                })
            }
            _ => Err(kimchi::circuits::expr::ExprError::MissingEvaluation(
                col,
                CurrOrNext::Curr,
            )),
        }
    }
}

/// Vendored evaluate function for PolishToken with feature flags treated as disabled.
/// See module-level comment for rationale.
///
/// Parameters:
/// - `vanishes_on_zk`: Pre-computed value for VanishesOnZeroKnowledgeAndPreviousRows
/// - `domain` and `pt`: Used to compute UnnormalizedLagrangeBasis on the fly
fn evaluate_polish_tokens<
    F: FftField,
    Col: Copy + std::fmt::Debug,
    ChallengeTerm: Copy,
    Evals: ColumnEvaluations<F, Column = Col>,
>(
    toks: &[PolishToken<F, Col, ChallengeTerm>],
    domain: Radix2EvaluationDomain<F>,
    pt: F,
    vanishes_on_zk: F,
    evals: &Evals,
    c: &Constants<F>,
    chals: &dyn Index<ChallengeTerm, Output = F>,
) -> std::result::Result<F, ExprError<Col>> {
    let mut stack: Vec<F> = vec![];
    let mut cache: Vec<F> = vec![];
    let mut skip_count = 0;

    for t in toks.iter() {
        if skip_count > 0 {
            skip_count -= 1;
            continue;
        }

        use ConstantTerm::*;
        use PolishToken::*;
        match t {
            Challenge(challenge_term) => stack.push(chals[*challenge_term]),
            Constant(EndoCoefficient) => stack.push(c.endo_coefficient),
            Constant(Mds { row, col }) => stack.push(c.mds[*row][*col]),
            VanishesOnZeroKnowledgeAndPreviousRows => {
                stack.push(vanishes_on_zk);
            }
            UnnormalizedLagrangeBasis(i) => {
                // Compute (pt^n - 1) / (pt - ω^offset)
                // where offset accounts for zk_rows if i.zk_rows is true
                let actual_offset = if i.zk_rows {
                    (domain.size() as i32) - (c.zk_rows as i32) + i.offset
                } else {
                    i.offset
                };
                let omega_i = if actual_offset < 0 {
                    domain
                        .group_gen
                        .pow([(-actual_offset) as u64])
                        .inverse()
                        .expect("Group generator should be invertible")
                } else {
                    domain.group_gen.pow([actual_offset as u64])
                };
                let lagrange = domain.evaluate_vanishing_polynomial(pt) / (pt - omega_i);
                stack.push(lagrange);
            }
            Constant(Literal(x)) => stack.push(*x),
            Dup => stack.push(stack[stack.len() - 1]),
            Cell(v) => {
                // Inline Variable::evaluate since it's private in Kimchi
                let point_evaluations = evals.evaluate(v.col)?;
                let x = match v.row {
                    CurrOrNext::Curr => point_evaluations.zeta,
                    CurrOrNext::Next => point_evaluations.zeta_omega,
                };
                stack.push(x);
            }
            Pow(n) => {
                let i = stack.len() - 1;
                stack[i] = stack[i].pow([*n]);
            }
            Add => {
                let y = stack.pop().ok_or(ExprError::EmptyStack)?;
                let x = stack.pop().ok_or(ExprError::EmptyStack)?;
                stack.push(x + y);
            }
            Mul => {
                let y = stack.pop().ok_or(ExprError::EmptyStack)?;
                let x = stack.pop().ok_or(ExprError::EmptyStack)?;
                stack.push(x * y);
            }
            Sub => {
                let y = stack.pop().ok_or(ExprError::EmptyStack)?;
                let x = stack.pop().ok_or(ExprError::EmptyStack)?;
                stack.push(x - y);
            }
            Store => {
                let x = stack[stack.len() - 1];
                cache.push(x);
            }
            Load(i) => stack.push(cache[*i]),
            // Feature flags are all treated as DISABLED.
            //
            // The expression uses a pattern where each feature has:
            // - SkipIfNot(feat, N): large block with gate computation
            // - SkipIfNot(feat, 1): small block with zero constant
            // - Add: combines results
            //
            // When disabled:
            // - Large block: skip N tokens, DON'T push (the block would have
            //   produced a value that gets Added, but we skip it)
            // - Small block: skip 1 token, push zero (this provides the "else" value)
            // - Add: combines accumulator with zero
            //
            // The key insight: only SkipIfNot with count=1 should push zero.
            // Larger blocks skip their computation without pushing.
            SkipIf(_feature, _count) => {
                // Feature is disabled, so is_enabled() would return false.
                // Condition is false, so we do nothing - just continue to next token.
            }
            SkipIfNot(_feature, count) => {
                // Feature is disabled, so !is_enabled() would return true.
                skip_count = *count;
                // Only push zero for small blocks (the "else" value pattern)
                if *count <= 1 {
                    stack.push(F::zero());
                }
            }
        }
    }

    assert_eq!(
        stack.len(),
        1,
        "Stack should have exactly one element after evaluation"
    );
    Ok(stack[0])
}

/// Get the Pallas linearization constant term as Polish tokens
fn get_pallas_linearization() -> Vec<PolishToken<PallasBaseField, Column, BerkeleyChallengeTerm>> {
    let evaluated_cols = linearization_columns::<PallasBaseField>(None);
    let (expr, _powers_of_alpha) = constraints_expr::<PallasBaseField>(None, true);
    let linearization = expr.linearize(evaluated_cols).unwrap();
    linearization.constant_term.to_polish()
}

/// Get the Vesta linearization constant term as Polish tokens
fn get_vesta_linearization() -> Vec<PolishToken<VestaBaseField, Column, BerkeleyChallengeTerm>> {
    let evaluated_cols = linearization_columns::<VestaBaseField>(None);
    let (expr, _powers_of_alpha) = constraints_expr::<VestaBaseField>(None, true);
    let linearization = expr.linearize(evaluated_cols).unwrap();
    linearization.constant_term.to_polish()
}

/// Evaluate the Pallas linearization polynomial with given inputs
/// All field elements are passed as External<PallasBaseField> (= VestaScalarField = Pallas base field)
#[napi]
#[allow(clippy::too_many_arguments)]
pub fn evaluate_pallas_linearization(
    // Challenges
    alpha: &PallasBaseFieldExternal,
    beta: &PallasBaseFieldExternal,
    gamma: &PallasBaseFieldExternal,
    joint_combiner: &PallasBaseFieldExternal,
    // Witness evaluations: flattened array [col0_curr, col0_next, col1_curr, col1_next, ...]
    witness_evals: Vec<&PallasBaseFieldExternal>,
    // Coefficient evaluations
    coefficient_evals: Vec<&PallasBaseFieldExternal>,
    // Index evaluations [poseidon_curr, poseidon_next, generic_curr, generic_next, ...]
    poseidon_index: Vec<&PallasBaseFieldExternal>,
    generic_index: Vec<&PallasBaseFieldExternal>,
    varbasemul_index: Vec<&PallasBaseFieldExternal>,
    endomul_index: Vec<&PallasBaseFieldExternal>,
    endomul_scalar_index: Vec<&PallasBaseFieldExternal>,
    complete_add_index: Vec<&PallasBaseFieldExternal>,
    // Other inputs
    vanishes_on_zk: &PallasBaseFieldExternal,
    zeta: &PallasBaseFieldExternal,
    domain_log2: u32,
) -> Result<PallasBaseFieldExternal> {
    // Parse challenges
    let challenges = Challenges {
        alpha: **alpha,
        beta: **beta,
        gamma: **gamma,
        joint_combiner: **joint_combiner,
    };

    // Build column evaluations
    let mut evals = TestColumnEvaluations::<PallasBaseField>::new_zero();

    // Parse witness evaluations (flattened: [col0_curr, col0_next, col1_curr, ...])
    for col in 0..WITNESS_COLS {
        let base_idx = col * 2;
        if base_idx + 1 < witness_evals.len() {
            evals.witness[col][0] = **witness_evals[base_idx];
            evals.witness[col][1] = **witness_evals[base_idx + 1];
        }
    }

    // Parse coefficient evaluations
    for (i, coeff) in coefficient_evals.iter().enumerate().take(COEFF_COLS) {
        evals.coefficients[i] = ***coeff;
    }

    // Parse index evaluations
    use kimchi::circuits::gate::GateType;
    if poseidon_index.len() >= 2 {
        evals.index.insert(
            GateType::Poseidon,
            [**poseidon_index[0], **poseidon_index[1]],
        );
    }
    if generic_index.len() >= 2 {
        evals
            .index
            .insert(GateType::Generic, [**generic_index[0], **generic_index[1]]);
    }
    if varbasemul_index.len() >= 2 {
        evals.index.insert(
            GateType::VarBaseMul,
            [**varbasemul_index[0], **varbasemul_index[1]],
        );
    }
    if endomul_index.len() >= 2 {
        evals
            .index
            .insert(GateType::EndoMul, [**endomul_index[0], **endomul_index[1]]);
    }
    if endomul_scalar_index.len() >= 2 {
        evals.index.insert(
            GateType::EndoMulScalar,
            [**endomul_scalar_index[0], **endomul_scalar_index[1]],
        );
    }
    if complete_add_index.len() >= 2 {
        evals.index.insert(
            GateType::CompleteAdd,
            [**complete_add_index[0], **complete_add_index[1]],
        );
    }

    // Create domain
    let domain = Radix2EvaluationDomain::<PallasBaseField>::new(1 << domain_log2)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    // Create constants
    let (endo_q, _endo_r) = endos::<Pallas>();
    let params = fp_kimchi::static_params();
    let constants = Constants {
        endo_coefficient: endo_q,
        mds: &params.mds,
        zk_rows: 3,
    };

    // Get the linearization tokens
    let tokens = get_pallas_linearization();

    // Evaluate using our vendored function (see module-level comment for rationale)
    let result = evaluate_polish_tokens(
        &tokens,
        domain,
        **zeta,
        **vanishes_on_zk,
        &evals,
        &constants,
        &challenges,
    )
    .map_err(|e| Error::new(Status::GenericFailure, format!("Evaluation error: {e:?}")))?;

    Ok(External::new(result))
}

/// Evaluate the Vesta linearization polynomial with given inputs
/// All field elements are passed as External<VestaBaseField> (= PallasScalarField = Vesta base field)
#[napi]
#[allow(clippy::too_many_arguments)]
pub fn evaluate_vesta_linearization(
    // Challenges
    alpha: &VestaBaseFieldExternal,
    beta: &VestaBaseFieldExternal,
    gamma: &VestaBaseFieldExternal,
    joint_combiner: &VestaBaseFieldExternal,
    // Witness evaluations: flattened array [col0_curr, col0_next, col1_curr, col1_next, ...]
    witness_evals: Vec<&VestaBaseFieldExternal>,
    // Coefficient evaluations
    coefficient_evals: Vec<&VestaBaseFieldExternal>,
    // Index evaluations [poseidon_curr, poseidon_next, generic_curr, generic_next, ...]
    poseidon_index: Vec<&VestaBaseFieldExternal>,
    generic_index: Vec<&VestaBaseFieldExternal>,
    varbasemul_index: Vec<&VestaBaseFieldExternal>,
    endomul_index: Vec<&VestaBaseFieldExternal>,
    endomul_scalar_index: Vec<&VestaBaseFieldExternal>,
    complete_add_index: Vec<&VestaBaseFieldExternal>,
    // Other inputs
    vanishes_on_zk: &VestaBaseFieldExternal,
    zeta: &VestaBaseFieldExternal,
    domain_log2: u32,
) -> Result<VestaBaseFieldExternal> {
    // Parse challenges
    let challenges = Challenges {
        alpha: **alpha,
        beta: **beta,
        gamma: **gamma,
        joint_combiner: **joint_combiner,
    };

    // Build column evaluations
    let mut evals = TestColumnEvaluations::<VestaBaseField>::new_zero();

    // Parse witness evaluations (flattened: [col0_curr, col0_next, col1_curr, ...])
    for col in 0..WITNESS_COLS {
        let base_idx = col * 2;
        if base_idx + 1 < witness_evals.len() {
            evals.witness[col][0] = **witness_evals[base_idx];
            evals.witness[col][1] = **witness_evals[base_idx + 1];
        }
    }

    // Parse coefficient evaluations
    for (i, coeff) in coefficient_evals.iter().enumerate().take(COEFF_COLS) {
        evals.coefficients[i] = ***coeff;
    }

    // Parse index evaluations
    use kimchi::circuits::gate::GateType;
    if poseidon_index.len() >= 2 {
        evals.index.insert(
            GateType::Poseidon,
            [**poseidon_index[0], **poseidon_index[1]],
        );
    }
    if generic_index.len() >= 2 {
        evals
            .index
            .insert(GateType::Generic, [**generic_index[0], **generic_index[1]]);
    }
    if varbasemul_index.len() >= 2 {
        evals.index.insert(
            GateType::VarBaseMul,
            [**varbasemul_index[0], **varbasemul_index[1]],
        );
    }
    if endomul_index.len() >= 2 {
        evals
            .index
            .insert(GateType::EndoMul, [**endomul_index[0], **endomul_index[1]]);
    }
    if endomul_scalar_index.len() >= 2 {
        evals.index.insert(
            GateType::EndoMulScalar,
            [**endomul_scalar_index[0], **endomul_scalar_index[1]],
        );
    }
    if complete_add_index.len() >= 2 {
        evals.index.insert(
            GateType::CompleteAdd,
            [**complete_add_index[0], **complete_add_index[1]],
        );
    }

    // Create domain
    let domain = Radix2EvaluationDomain::<VestaBaseField>::new(1 << domain_log2)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    // Create constants
    let (endo_q, _endo_r) = endos::<Vesta>();
    let params = fq_kimchi::static_params();
    let constants = Constants {
        endo_coefficient: endo_q,
        mds: &params.mds,
        zk_rows: 3,
    };

    // Get the linearization tokens
    let tokens = get_vesta_linearization();

    // Evaluate using our vendored function (see module-level comment for rationale)
    let result = evaluate_polish_tokens(
        &tokens,
        domain,
        **zeta,
        **vanishes_on_zk,
        &evals,
        &constants,
        &challenges,
    )
    .map_err(|e| Error::new(Status::GenericFailure, format!("Evaluation error: {e:?}")))?;

    Ok(External::new(result))
}

/// Compute polynomial evaluations from a witness matrix.
///
/// Given a witness (15 columns of field values), this function:
/// 1. Pads each column to the domain size
/// 2. Interpolates each column into a polynomial
/// 3. Evaluates each polynomial at zeta and zeta*omega
///
/// This is useful for testing the linearization constraint check with valid witnesses,
/// without needing to create a full proof.
///
/// Returns: flattened array [col0_zeta, col0_zeta_omega, col1_zeta, col1_zeta_omega, ...]
#[napi]
pub fn pallas_witness_to_evaluations(
    witness: Vec<Vec<&PallasBaseFieldExternal>>,
    zeta: &PallasBaseFieldExternal,
    domain_log2: u32,
) -> Result<Vec<PallasBaseFieldExternal>> {
    if witness.len() != COLUMNS {
        return Err(Error::new(
            Status::InvalidArg,
            format!("Expected {} witness columns, got {}", COLUMNS, witness.len()),
        ));
    }

    // Create domain
    let domain_size = 1usize << domain_log2;
    let domain = Radix2EvaluationDomain::<PallasBaseField>::new(domain_size)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    let zeta_val = **zeta;
    let omega = domain.group_gen;
    let zeta_omega = zeta_val * omega;

    let mut result = Vec::with_capacity(COLUMNS * 2);

    for col in 0..COLUMNS {
        // Pad column to domain size
        let mut col_evals: Vec<PallasBaseField> = witness[col].iter().map(|x| ***x).collect();
        col_evals.resize(domain_size, PallasBaseField::zero());

        // Interpolate to get polynomial
        let poly = Evaluations::from_vec_and_domain(col_evals, domain).interpolate();

        // Evaluate at zeta and zeta*omega
        let eval_zeta = poly.evaluate(&zeta_val);
        let eval_zeta_omega = poly.evaluate(&zeta_omega);

        result.push(External::new(eval_zeta));
        result.push(External::new(eval_zeta_omega));
    }

    Ok(result)
}

/// Compute polynomial evaluations from a witness matrix (Vesta version).
#[napi]
pub fn vesta_witness_to_evaluations(
    witness: Vec<Vec<&VestaBaseFieldExternal>>,
    zeta: &VestaBaseFieldExternal,
    domain_log2: u32,
) -> Result<Vec<VestaBaseFieldExternal>> {
    if witness.len() != COLUMNS {
        return Err(Error::new(
            Status::InvalidArg,
            format!("Expected {} witness columns, got {}", COLUMNS, witness.len()),
        ));
    }

    // Create domain
    let domain_size = 1usize << domain_log2;
    let domain = Radix2EvaluationDomain::<VestaBaseField>::new(domain_size)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    let zeta_val = **zeta;
    let omega = domain.group_gen;
    let zeta_omega = zeta_val * omega;

    let mut result = Vec::with_capacity(COLUMNS * 2);

    for col in 0..COLUMNS {
        // Pad column to domain size
        let mut col_evals: Vec<VestaBaseField> = witness[col].iter().map(|x| ***x).collect();
        col_evals.resize(domain_size, VestaBaseField::zero());

        // Interpolate to get polynomial
        let poly = Evaluations::from_vec_and_domain(col_evals, domain).interpolate();

        // Evaluate at zeta and zeta*omega
        let eval_zeta = poly.evaluate(&zeta_val);
        let eval_zeta_omega = poly.evaluate(&zeta_omega);

        result.push(External::new(eval_zeta));
        result.push(External::new(eval_zeta_omega));
    }

    Ok(result)
}

/// Compute coefficient polynomial evaluations from Vesta circuit gates.
///
/// For Pallas linearization (which verifies Vesta circuits), we need coefficient
/// evaluations in Fp (= Pallas.BaseField = Vesta.ScalarField).
///
/// This takes Vesta gates (which have coefficients in Fp) and interpolates
/// each coefficient column into a polynomial, then evaluates at zeta.
///
/// Returns: array of 15 coefficient evaluations at zeta
#[napi]
pub fn pallas_gates_to_coefficient_evaluations(
    gates: Vec<&VestaCircuitGateExternal>,
    zeta: &PallasBaseFieldExternal,
    domain_log2: u32,
) -> Result<Vec<PallasBaseFieldExternal>> {
    let domain_size = 1usize << domain_log2;
    let domain = Radix2EvaluationDomain::<PallasBaseField>::new(domain_size)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    let zeta_val = **zeta;
    let num_gates = gates.len();

    // Initialize coefficient columns (15 columns, one per coefficient index)
    let mut coeff_columns: Vec<Vec<PallasBaseField>> = vec![vec![PallasBaseField::zero(); num_gates]; COEFF_COLS];

    // Extract coefficients from each gate into columns
    for (row, gate) in gates.iter().enumerate() {
        for (col_idx, coeff) in gate.coeffs.iter().enumerate() {
            if col_idx < COEFF_COLS {
                coeff_columns[col_idx][row] = *coeff;
            }
        }
    }

    // Interpolate and evaluate each coefficient column
    let mut result = Vec::with_capacity(COEFF_COLS);
    for col_idx in 0..COEFF_COLS {
        // Pad to domain size
        let mut col_evals = coeff_columns[col_idx].clone();
        col_evals.resize(domain_size, PallasBaseField::zero());

        // Interpolate to polynomial
        let poly = Evaluations::from_vec_and_domain(col_evals, domain).interpolate();

        // Evaluate at zeta (coefficient polynomials only need zeta, not zeta*omega)
        let eval_zeta = poly.evaluate(&zeta_val);
        result.push(External::new(eval_zeta));
    }

    Ok(result)
}

/// Compute selector polynomial evaluations from Vesta circuit gates.
///
/// Selector polynomials are indicator polynomials that are 1 at rows where
/// a specific gate type is used and 0 elsewhere.
///
/// Returns: flattened array [poseidon_zeta, poseidon_zeta_omega, generic_zeta, generic_zeta_omega,
///          varbasemul_zeta, varbasemul_zeta_omega, endomul_zeta, endomul_zeta_omega,
///          endomul_scalar_zeta, endomul_scalar_zeta_omega, complete_add_zeta, complete_add_zeta_omega]
#[napi]
pub fn pallas_gates_to_selector_evaluations(
    gates: Vec<&VestaCircuitGateExternal>,
    zeta: &PallasBaseFieldExternal,
    domain_log2: u32,
) -> Result<Vec<PallasBaseFieldExternal>> {
    use kimchi::circuits::gate::GateType;

    let domain_size = 1usize << domain_log2;
    let domain = Radix2EvaluationDomain::<PallasBaseField>::new(domain_size)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    let zeta_val = **zeta;
    let omega = domain.group_gen;
    let zeta_omega = zeta_val * omega;

    // Gate types we need selectors for (in order)
    let gate_types = [
        GateType::Poseidon,
        GateType::Generic,
        GateType::VarBaseMul,
        GateType::EndoMul,
        GateType::EndoMulScalar,
        GateType::CompleteAdd,
    ];

    let mut result = Vec::with_capacity(gate_types.len() * 2);

    for gate_type in gate_types.iter() {
        // Build selector column: 1 where gate matches, 0 elsewhere
        let mut selector: Vec<PallasBaseField> = gates
            .iter()
            .map(|g| {
                if g.typ == *gate_type {
                    PallasBaseField::from(1u64)
                } else {
                    PallasBaseField::zero()
                }
            })
            .collect();

        // Pad to domain size
        selector.resize(domain_size, PallasBaseField::zero());

        // Interpolate to polynomial
        let poly = Evaluations::from_vec_and_domain(selector, domain).interpolate();

        // Evaluate at zeta and zeta*omega
        let eval_zeta = poly.evaluate(&zeta_val);
        let eval_zeta_omega = poly.evaluate(&zeta_omega);

        result.push(External::new(eval_zeta));
        result.push(External::new(eval_zeta_omega));
    }

    Ok(result)
}

/// Compute coefficient polynomial evaluations from Pallas circuit gates.
///
/// For Vesta linearization (which verifies Pallas circuits), we need coefficient
/// evaluations in Fq (= Vesta.BaseField = Pallas.ScalarField).
#[napi]
pub fn vesta_gates_to_coefficient_evaluations(
    gates: Vec<&PallasCircuitGateExternal>,
    zeta: &VestaBaseFieldExternal,
    domain_log2: u32,
) -> Result<Vec<VestaBaseFieldExternal>> {
    let domain_size = 1usize << domain_log2;
    let domain = Radix2EvaluationDomain::<VestaBaseField>::new(domain_size)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    let zeta_val = **zeta;
    let num_gates = gates.len();

    // Initialize coefficient columns
    let mut coeff_columns: Vec<Vec<VestaBaseField>> = vec![vec![VestaBaseField::zero(); num_gates]; COEFF_COLS];

    // Extract coefficients from each gate into columns
    for (row, gate) in gates.iter().enumerate() {
        for (col_idx, coeff) in gate.coeffs.iter().enumerate() {
            if col_idx < COEFF_COLS {
                coeff_columns[col_idx][row] = *coeff;
            }
        }
    }

    // Interpolate and evaluate each coefficient column
    let mut result = Vec::with_capacity(COEFF_COLS);
    for col_idx in 0..COEFF_COLS {
        let mut col_evals = coeff_columns[col_idx].clone();
        col_evals.resize(domain_size, VestaBaseField::zero());
        let poly = Evaluations::from_vec_and_domain(col_evals, domain).interpolate();
        let eval_zeta = poly.evaluate(&zeta_val);
        result.push(External::new(eval_zeta));
    }

    Ok(result)
}

/// Compute selector polynomial evaluations from Pallas circuit gates.
#[napi]
pub fn vesta_gates_to_selector_evaluations(
    gates: Vec<&PallasCircuitGateExternal>,
    zeta: &VestaBaseFieldExternal,
    domain_log2: u32,
) -> Result<Vec<VestaBaseFieldExternal>> {
    use kimchi::circuits::gate::GateType;

    let domain_size = 1usize << domain_log2;
    let domain = Radix2EvaluationDomain::<VestaBaseField>::new(domain_size)
        .ok_or_else(|| Error::new(Status::InvalidArg, "Invalid domain size"))?;

    let zeta_val = **zeta;
    let omega = domain.group_gen;
    let zeta_omega = zeta_val * omega;

    let gate_types = [
        GateType::Poseidon,
        GateType::Generic,
        GateType::VarBaseMul,
        GateType::EndoMul,
        GateType::EndoMulScalar,
        GateType::CompleteAdd,
    ];

    let mut result = Vec::with_capacity(gate_types.len() * 2);

    for gate_type in gate_types.iter() {
        let mut selector: Vec<VestaBaseField> = gates
            .iter()
            .map(|g| {
                if g.typ == *gate_type {
                    VestaBaseField::from(1u64)
                } else {
                    VestaBaseField::zero()
                }
            })
            .collect();

        selector.resize(domain_size, VestaBaseField::zero());
        let poly = Evaluations::from_vec_and_domain(selector, domain).interpolate();
        let eval_zeta = poly.evaluate(&zeta_val);
        let eval_zeta_omega = poly.evaluate(&zeta_omega);

        result.push(External::new(eval_zeta));
        result.push(External::new(eval_zeta_omega));
    }

    Ok(result)
}

