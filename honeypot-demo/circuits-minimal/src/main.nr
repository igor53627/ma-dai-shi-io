// Minimal honeypot verifier for testing proof generation flow
// Simplified version with smaller inputs

fn main(
    // Public inputs
    seed_hash: pub Field,
    output_valid: pub Field,
    
    // Private witness: simplified 4-word seed
    seed: [Field; 4]
) {
    // Simple hash of seed
    let mut hash: Field = 0;
    for i in 0..4 {
        hash = hash + seed[i] * ((i + 1) as Field);
    }
    
    // Verify hash matches public commitment
    assert(hash == seed_hash);
    
    // Output must be 1 (valid seed found)
    assert(output_valid == 1);
}

#[test]
fn test_valid_seed() {
    // seed = [1, 2, 3, 4]
    // hash = 1*1 + 2*2 + 3*3 + 4*4 = 1 + 4 + 9 + 16 = 30
    let seed: [Field; 4] = [1, 2, 3, 4];
    let hash: Field = 30;
    
    main(hash, 1, seed);
}
