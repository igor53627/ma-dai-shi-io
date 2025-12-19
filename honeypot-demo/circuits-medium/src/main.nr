// Medium-sized honeypot verifier (16 BP steps instead of 128)
// Good balance of security demo vs proof generation speed

global FIELD_MOD: u32 = 251;
global BP_STEPS: u32 = 16;

fn main(
    // Public inputs
    obf_prog_hash: pub Field,
    evaluation_output: pub Field,
    
    // Private witness
    seed_phrase: [Field; 12],
    bp_matrices_flat: [Field; 400]  // 16 steps x 25 entries
) {
    // 1. Verify commitment
    let computed_hash = simple_hash(bp_matrices_flat);
    assert(computed_hash == obf_prog_hash);
    
    // 2. Encode seed to bits (first 16 bits)
    let input_bits = encode_seed_to_bits_16(seed_phrase);
    
    // 3. Evaluate 16-step matrix BP
    let bp_result = evaluate_matrix_bp_16(input_bits, bp_matrices_flat);
    
    // 4. Verify output
    assert(bp_result == evaluation_output);
    assert(evaluation_output == 1);
}

fn encode_seed_to_bits_16(seed: [Field; 12]) -> [u8; 16] {
    let mut bits: [u8; 16] = [0; 16];
    let word = seed[0] as u32;
    
    for j in 0..11 {
        if j < 16 {
            let shift = 10 - j;
            let bit = (word >> shift) & 1;
            bits[j] = bit as u8;
        }
    }
    
    // Fill remaining from second word
    let word2 = seed[1] as u32;
    for j in 0..5 {
        let idx = 11 + j;
        if idx < 16 {
            let shift = 10 - j;
            let bit = (word2 >> shift) & 1;
            bits[idx] = bit as u8;
        }
    }
    
    bits
}

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

fn identity_matrix() -> [u32; 25] {
    [
        1, 0, 0, 0, 0,
        0, 1, 0, 0, 0,
        0, 0, 1, 0, 0,
        0, 0, 0, 1, 0,
        0, 0, 0, 0, 1
    ]
}

fn get_matrix_16(matrices: [Field; 400], step: u32) -> [u32; 25] {
    let mut m: [u32; 25] = [0; 25];
    let base = step * 25;
    
    for i in 0..25 {
        m[i] = matrices[base + i] as u32;
    }
    
    m
}

fn evaluate_matrix_bp_16(input: [u8; 16], matrices: [Field; 400]) -> Field {
    let mut result = identity_matrix();
    
    for i in 0..16 {
        if input[i] == 1 {
            let m = get_matrix_16(matrices, i as u32);
            result = matrix_mul(result, m);
        }
    }
    
    let id = identity_matrix();
    let mut is_identity: bool = true;
    
    for i in 0..25 {
        if result[i] != id[i] {
            is_identity = false;
        }
    }
    
    if is_identity { 1 } else { 0 }
}

fn simple_hash(arr: [Field; 400]) -> Field {
    let mut acc: Field = 0;
    for i in 0..16 {
        let idx = i * 25;
        acc = acc + arr[idx] * (i as Field + 1);
    }
    acc
}

#[test]
fn test_valid_seed() {
    // All identity matrices, seed with all zeros -> output 1
    let mut matrices: [Field; 400] = [0; 400];
    
    // Set up identity matrices
    for step in 0..16 {
        let base = step * 25;
        matrices[base + 0] = 1;
        matrices[base + 6] = 1;
        matrices[base + 12] = 1;
        matrices[base + 18] = 1;
        matrices[base + 24] = 1;
    }
    
    let hash = simple_hash(matrices);
    let seed: [Field; 12] = [0; 12];
    
    main(hash, 1, seed, matrices);
}
