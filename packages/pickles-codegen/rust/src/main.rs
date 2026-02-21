//! Generate JSON files containing the Kimchi constraint linearization polynomials.
//!
//! Environment variables:
//!   - LINEARIZATION_JSON_DIR: Directory to write output files
//!
//! Outputs:
//!   - $LINEARIZATION_JSON_DIR/pallas_scalar_field.json
//!   - $LINEARIZATION_JSON_DIR/vesta_scalar_field.json

use ark_ff::PrimeField;
use kimchi::{
    circuits::{
        berkeley_columns::{BerkeleyChallengeTerm, Column},
        expr::{ConstantTerm, Linearization, PolishToken, RowOffset},
        gate::CurrOrNext,
    },
    linearization::{constraints_expr, linearization_columns},
};
use serde::{Deserialize, Serialize};
use std::{env, fs, path::Path};

/// A version of ConstantTerm where field elements are hex strings
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ConstantTermHex {
    EndoCoefficient,
    Mds { row: usize, col: usize },
    Literal(String),
}

/// A version of PolishToken where field elements are hex strings
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum PolishTokenHex {
    Constant(ConstantTermHex),
    Challenge(BerkeleyChallengeTerm),
    Cell { col: Column, row: CurrOrNext },
    Dup,
    Pow(u64),
    Add,
    Mul,
    Sub,
    VanishesOnZeroKnowledgeAndPreviousRows,
    UnnormalizedLagrangeBasis(RowOffset),
    Store,
    Load(usize),
    SkipIf(kimchi::circuits::expr::FeatureFlag, usize),
    SkipIfNot(kimchi::circuits::expr::FeatureFlag, usize),
}

fn constant_term_to_hex<F: PrimeField>(term: &ConstantTerm<F>) -> ConstantTermHex {
    match term {
        ConstantTerm::EndoCoefficient => ConstantTermHex::EndoCoefficient,
        ConstantTerm::Mds { row, col } => ConstantTermHex::Mds {
            row: *row,
            col: *col,
        },
        ConstantTerm::Literal(x) => {
            let bigint: num_bigint::BigUint = (*x).into_bigint().into();
            let hex_str = format!("{bigint:X}");
            // Ensure even number of hex digits for proper parsing
            let padded = if hex_str.len() % 2 == 1 {
                format!("0x0{hex_str}")
            } else {
                format!("0x{hex_str}")
            };
            ConstantTermHex::Literal(padded)
        }
    }
}

fn polish_token_to_hex<F: PrimeField>(
    token: &PolishToken<F, Column, BerkeleyChallengeTerm>,
) -> PolishTokenHex {
    match token {
        PolishToken::Constant(term) => PolishTokenHex::Constant(constant_term_to_hex(term)),
        PolishToken::Challenge(c) => PolishTokenHex::Challenge(*c),
        PolishToken::Cell(var) => PolishTokenHex::Cell {
            col: var.col,
            row: var.row,
        },
        PolishToken::Dup => PolishTokenHex::Dup,
        PolishToken::Pow(n) => PolishTokenHex::Pow(*n),
        PolishToken::Add => PolishTokenHex::Add,
        PolishToken::Mul => PolishTokenHex::Mul,
        PolishToken::Sub => PolishTokenHex::Sub,
        PolishToken::VanishesOnZeroKnowledgeAndPreviousRows => {
            PolishTokenHex::VanishesOnZeroKnowledgeAndPreviousRows
        }
        PolishToken::UnnormalizedLagrangeBasis(offset) => {
            PolishTokenHex::UnnormalizedLagrangeBasis(*offset)
        }
        PolishToken::Store => PolishTokenHex::Store,
        PolishToken::Load(i) => PolishTokenHex::Load(*i),
        PolishToken::SkipIf(flag, count) => PolishTokenHex::SkipIf(*flag, *count),
        PolishToken::SkipIfNot(flag, count) => PolishTokenHex::SkipIfNot(*flag, *count),
    }
}

fn polish_tokens_to_hex<F: PrimeField>(
    tokens: &[PolishToken<F, Column, BerkeleyChallengeTerm>],
) -> Vec<PolishTokenHex> {
    tokens.iter().map(polish_token_to_hex).collect()
}

fn generate_linearization_json<F: PrimeField>() -> String {
    // Get the constraint expression with all features enabled (None = all optional gates)
    let evaluated_cols = linearization_columns::<F>(None);
    let (expr, _powers_of_alpha) = constraints_expr::<F>(None, true);

    // Linearize the expression
    let linearization = expr.linearize(evaluated_cols).unwrap();

    // Convert to compact polish notation and then to hex representation.
    // to_polish() uses Store/Load for shared subexpressions, producing fewer tokens.
    let constant_polish = polish_tokens_to_hex(&linearization.constant_term.to_polish());
    let index_polish: Vec<_> = linearization
        .index_terms
        .into_iter()
        .map(|(col, expr)| (col, polish_tokens_to_hex(&expr.to_polish())))
        .collect();

    // Create a serializable structure
    let output = Linearization {
        constant_term: constant_polish,
        index_terms: index_polish,
    };

    serde_json::to_string_pretty(&output).expect("Failed to serialize linearization")
}

fn main() {
    let output_dir_str = env::var("LINEARIZATION_JSON_DIR")
        .expect("LINEARIZATION_JSON_DIR environment variable not set");

    let output_dir = Path::new(&output_dir_str);

    if !output_dir.exists() {
        fs::create_dir_all(output_dir).expect("Failed to create output directory");
    }

    // Generate for Pallas scalar field (Fp)
    println!("Generating linearization for Pallas scalar field...");
    let pallas_json = generate_linearization_json::<mina_curves::pasta::Fp>();
    let pallas_path = output_dir.join("pallas_scalar_field.json");
    fs::write(&pallas_path, &pallas_json).expect("Failed to write Pallas linearization");
    println!("Wrote {}", pallas_path.display());

    // Generate for Vesta scalar field (Fq)
    println!("Generating linearization for Vesta scalar field...");
    let vesta_json = generate_linearization_json::<mina_curves::pasta::Fq>();
    let vesta_path = output_dir.join("vesta_scalar_field.json");
    fs::write(&vesta_path, &vesta_json).expect("Failed to write Vesta linearization");
    println!("Wrote {}", vesta_path.display());

    println!("Done!");
}
