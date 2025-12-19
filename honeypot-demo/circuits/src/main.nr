// Ma-Dai-Shi Honeypot Verifier
// 
// Proves: "I know a 12-word seed phrase that, when evaluated through
// the obfuscated Ma-Dai-Shi program, outputs 1 (valid match)"
//
// Issue #59: https://github.com/igor53627/circuit-mixing-research/issues/59

// ============================================================================
// Constants
// ============================================================================

// Field modulus for matrix operations (same as Rust MatrixBP)
global FIELD_MOD: u32 = 251;
global BP_STEPS: u32 = 128;

// ============================================================================
// Main Entry Point
// ============================================================================

fn main(
    // Public inputs (visible on-chain)
    obf_prog_hash: pub Field,       // Pedersen hash of serialized ObfProg
    evaluation_output: pub Field,   // Must be 1 for valid seed
    
    // Private witness (hidden from verifier)
    seed_phrase: [Field; 12],       // The 12 BIP-39 word indices (0-2047)
    bp_matrices_flat: [Field; 3200] // 128 steps x 25 entries per 5x5 matrix
) {
    // 1. Verify ObfProg commitment (simplified - use std::hash in production)
    let computed_hash = simple_hash(bp_matrices_flat);
    assert(computed_hash == obf_prog_hash);
    
    // 2. Encode seed phrase to bit vector (input to circuit)
    let input_bits = encode_seed_to_bits(seed_phrase);
    
    // 3. Evaluate Matrix Branching Program (core of base iO)
    let bp_result = evaluate_matrix_bp(input_bits, bp_matrices_flat);
    
    // 4. Check result matches claimed output
    assert(bp_result == evaluation_output);
    
    // 5. Honeypot condition: output must be 1 (found valid seed)
    assert(evaluation_output == 1);
}

// ============================================================================
// Seed Phrase Encoding
// ============================================================================

// Convert 12 BIP-39 word indices to 128-bit input vector
fn encode_seed_to_bits(seed: [Field; 12]) -> [u8; 128] {
    let mut bits: [u8; 128] = [0; 128];
    
    // Each word is 11 bits, total 132 bits, we use first 128
    for i in 0..11 {
        let word = seed[i] as u32;
        for j in 0..11 {
            let bit_idx = i * 11 + j;
            if bit_idx < 128 {
                // Extract bit j from word (MSB first)
                let shift = 10 - j;
                let bit = (word >> shift) & 1;
                bits[bit_idx] = bit as u8;
            }
        }
    }
    
    bits
}

// ============================================================================
// Matrix Branching Program Evaluation
// ============================================================================

// 5x5 matrix multiplication mod 251
fn matrix_mul(a: [u32; 25], b: [u32; 25]) -> [u32; 25] {
    let mut result: [u32; 25] = [0; 25];
    
    for i in 0..5 {
        for j in 0..5 {
            let mut sum: u32 = 0;
            for k in 0..5 {
                let a_idx = i * 5 + k;
                let b_idx = k * 5 + j;
                sum = sum + a[a_idx] * b[b_idx];
            }
            let out_idx = i * 5 + j;
            result[out_idx] = sum % FIELD_MOD;
        }
    }
    
    result
}

// Identity matrix as flat array
fn identity_matrix() -> [u32; 25] {
    [
        1, 0, 0, 0, 0,
        0, 1, 0, 0, 0,
        0, 0, 1, 0, 0,
        0, 0, 0, 1, 0,
        0, 0, 0, 0, 1
    ]
}

// Extract matrix at step i from flat array
fn get_matrix(matrices: [Field; 3200], step: u32) -> [u32; 25] {
    let mut m: [u32; 25] = [0; 25];
    let base = step * 25;
    
    for i in 0..25 {
        m[i] = matrices[base + i] as u32;
    }
    
    m
}

// Evaluate branching program on input bits
fn evaluate_matrix_bp(
    input: [u8; 128],
    matrices: [Field; 3200]
) -> Field {
    let mut result = identity_matrix();
    
    // For each input bit, multiply by corresponding matrix if bit is 1
    for i in 0..128 {
        if input[i] == 1 {
            let m = get_matrix(matrices, i as u32);
            result = matrix_mul(result, m);
        }
    }
    
    // Output: 1 if result equals identity, 0 otherwise
    let id = identity_matrix();
    let mut is_identity: bool = true;
    
    for i in 0..25 {
        if result[i] != id[i] {
            is_identity = false;
        }
    }
    
    if is_identity { 1 } else { 0 }
}

// ============================================================================
// Hash Functions
// ============================================================================

// Simple hash for commitment (use std::hash::pedersen in production)
fn simple_hash(arr: [Field; 3200]) -> Field {
    let mut acc: Field = 0;
    // Sample every 32nd element to keep circuit small
    for i in 0..100 {
        let idx = i * 32;
        acc = acc + arr[idx] * (i as Field + 1);
    }
    acc
}

// ============================================================================
// Tests
// ============================================================================

#[test]
fn test_identity_matrix() {
    let id = identity_matrix();
    assert(id[0] == 1);
    assert(id[6] == 1);  // [1][1]
    assert(id[12] == 1); // [2][2]
    assert(id[1] == 0);
}

#[test]
fn test_matrix_mul_identity() {
    let id = identity_matrix();
    let result = matrix_mul(id, id);
    
    // id * id = id
    for i in 0..25 {
        assert(result[i] == id[i]);
    }
}

#[test]
fn test_encode_seed() {
    // Test with seed where first word is 0
    let seed: [Field; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
    let bits = encode_seed_to_bits(seed);
    
    // First word is 0, so first 11 bits should be 0
    for i in 0..11 {
        assert(bits[i] == 0);
    }
}

#[test]
fn test_encode_seed_nonzero() {
    // Word 2047 = 0b11111111111 (all 1s in 11 bits)
    let seed: [Field; 12] = [2047, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let bits = encode_seed_to_bits(seed);
    
    // First 11 bits should all be 1
    for i in 0..11 {
        assert(bits[i] == 1);
    }
}
