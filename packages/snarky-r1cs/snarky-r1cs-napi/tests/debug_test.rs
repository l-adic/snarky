use ark_pallas::{Fr, Projective};
use bulletproofs::circuit::{prove, verify, types::{CRS, Circuit, Statement, Witness}};
use rand::rngs::OsRng;
use spongefish::domain_separator;

#[test] 
fn test_bulletproof_generated_circuit() {
    // Test using bulletproof's own generate_from_witness like their tests do
    let mut rng = OsRng;
    let q = 19;
    let n = 10; 
    let m = 1;
    
    let (circuit, witness) = Circuit::<Fr>::generate_from_witness(q, n, m, &mut rng);
    
    println!("Generated circuit satisfied by witness: {}", circuit.is_satisfied_by(&witness));
    
    let crs: CRS<Projective> = CRS::rand(circuit.n(), &mut rng);
    let statement = Statement::new(&crs, &witness);
    
    let domain_separator = domain_separator!("test-circuit-proof").instance(&statement.v);
    let mut prover_state = domain_separator.std_prover();
    let proof = prove(&mut prover_state, &crs, &circuit, &witness, &mut rng);
    
    println!("Proof generated, size: {}", proof.len());
    
    let mut verifier_state = domain_separator.std_verifier(&proof);
    match verify(&mut verifier_state, &crs, &circuit, &statement) {
        Ok(_) => println!("Generated circuit verification succeeded!"),
        Err(e) => println!("Generated circuit verification failed: {:?}", e),
    }
}

#[test]
fn test_purescript_generated_circuit() {
    let mut rng = OsRng;
    
    // Create a minimal circuit that matches our pattern
    let q = 19; // number of constraints  
    let n = 10; // number of multiplication gates
    let m = 1;  // number of public inputs
    
    // Create simple test matrices (all zeros for now, we'll refine based on actual values)
    let w_l = vec![vec![Fr::from(0u64); n]; q];
    let w_r = vec![vec![Fr::from(0u64); n]; q]; 
    let w_o = vec![vec![Fr::from(0u64); n]; q];
    let w_v = vec![vec![Fr::from(0u64); m]; q];
    let c = vec![Fr::from(0u64); q];
    
    let circuit = Circuit::new(w_l, w_r, w_o, w_v, c);
    
    // Create witness with representative values
    let mut a_l = vec![Fr::from(0u64); n];
    a_l[0] = Fr::from(12345u64);
    a_l[1] = Fr::from(1u64);
    
    let a_r = vec![Fr::from(1u64); n];
    
    let mut a_o = vec![Fr::from(0u64); n]; 
    a_o[0] = Fr::from(12345u64);
    a_o[1] = Fr::from(1u64);
    
    let v = vec![Fr::from(54321u64)];
    
    let witness = Witness::new(a_l, a_r, a_o, v, &mut rng);
    
    println!("Manual circuit satisfied by witness: {}", circuit.is_satisfied_by(&witness));
    
    let crs: CRS<Projective> = CRS::rand(n, &mut rng); // Use n for manual test
    let statement = Statement::new(&crs, &witness);
    
    let domain_separator = domain_separator!("test-circuit-proof").instance(&statement.v);
    let mut prover_state = domain_separator.std_prover();
    let proof = prove(&mut prover_state, &crs, &circuit, &witness, &mut rng);
    
    println!("Proof generated, size: {}", proof.len());
    
    let mut verifier_state = domain_separator.std_verifier(&proof);
    match verify(&mut verifier_state, &crs, &circuit, &statement) {
        Ok(_) => println!("Manual circuit verification succeeded!"),
        Err(e) => println!("Manual circuit verification failed: {:?}", e),
    }
}