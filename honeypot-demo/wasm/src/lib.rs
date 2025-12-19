//! Ma-Dai-Shi iO Evaluator - WASM Build
//!
//! Browser-based evaluation of obfuscated programs for the honeypot demo.
//! Users try seed phrase guesses in their browser; when they find a match,
//! they generate a zkSNARK proof to claim the on-chain prize.
//!
//! Issue #59: https://github.com/igor53627/circuit-mixing-research/issues/59

use wasm_bindgen::prelude::*;
use serde::{Deserialize, Serialize};

// ============================================================================
// WASM Bindings
// ============================================================================

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

macro_rules! console_log {
    ($($t:tt)*) => (log(&format_args!($($t)*).to_string()))
}

/// Initialize panic hook for better error messages
#[wasm_bindgen(start)]
pub fn init() {
    #[cfg(feature = "console_error_panic_hook")]
    console_error_panic_hook::set_once();
    console_log!("[honeypot-wasm] Initialized");
}

// ============================================================================
// Types
// ============================================================================

/// Serialized Ma-Dai-Shi obfuscated program
#[derive(Serialize, Deserialize, Clone)]
pub struct ObfuscatedProgram {
    /// Program hash (commitment)
    pub hash: [u8; 32],
    /// Matrix branching program steps
    pub bp_matrices: Vec<[[u8; 5]; 5]>,
    /// Number of input bits
    pub input_bits: usize,
}

/// Result of evaluating the obfuscated program
#[derive(Serialize, Deserialize)]
pub struct EvalResult {
    /// Whether the seed phrase is valid (output == 1)
    pub is_valid: bool,
    /// Raw output value
    pub output: u64,
    /// Evaluation time in milliseconds
    pub time_ms: f64,
}

/// Witness data needed for zkSNARK proof generation
#[derive(Serialize, Deserialize)]
pub struct ProofWitness {
    /// The seed phrase (12 word indices)
    pub seed_phrase: [u16; 12],
    /// Serialized obfuscated program
    pub obf_prog: Vec<u8>,
    /// Matrix BP intermediate values (for proof)
    pub bp_trace: Vec<[[u8; 5]; 5]>,
}

// ============================================================================
// Core Functions
// ============================================================================

/// Evaluate the obfuscated program on a seed phrase guess
///
/// Returns EvalResult indicating if the seed is valid
#[wasm_bindgen]
pub fn evaluate_seed(obf_prog_js: JsValue, seed_phrase_js: JsValue) -> Result<JsValue, JsValue> {
    let start = js_sys::Date::now();
    
    // Parse inputs
    let obf_prog: ObfuscatedProgram = serde_wasm_bindgen::from_value(obf_prog_js)
        .map_err(|e| JsValue::from_str(&format!("Invalid ObfProg: {}", e)))?;
    
    let seed_phrase: [u16; 12] = serde_wasm_bindgen::from_value(seed_phrase_js)
        .map_err(|e| JsValue::from_str(&format!("Invalid seed phrase: {}", e)))?;
    
    console_log!("[honeypot-wasm] Evaluating seed phrase...");
    
    // Convert seed phrase to input bits (128 bits from 12 words × 11 bits)
    let input_bits = encode_seed_to_bits(&seed_phrase);
    
    // Evaluate matrix branching program
    let output = evaluate_matrix_bp(&input_bits, &obf_prog.bp_matrices);
    
    let elapsed = js_sys::Date::now() - start;
    
    let result = EvalResult {
        is_valid: output == 1,
        output,
        time_ms: elapsed,
    };
    
    if result.is_valid {
        console_log!("[honeypot-wasm] FOUND VALID SEED!");
    }
    
    serde_wasm_bindgen::to_value(&result)
        .map_err(|e| JsValue::from_str(&format!("Serialization error: {}", e)))
}

/// Generate witness data for zkSNARK proof
///
/// Call this after finding a valid seed to prepare data for Noir prover
#[wasm_bindgen]
pub fn generate_witness(obf_prog_js: JsValue, seed_phrase_js: JsValue) -> Result<JsValue, JsValue> {
    let obf_prog: ObfuscatedProgram = serde_wasm_bindgen::from_value(obf_prog_js)
        .map_err(|e| JsValue::from_str(&format!("Invalid ObfProg: {}", e)))?;
    
    let seed_phrase: [u16; 12] = serde_wasm_bindgen::from_value(seed_phrase_js)
        .map_err(|e| JsValue::from_str(&format!("Invalid seed phrase: {}", e)))?;
    
    console_log!("[honeypot-wasm] Generating proof witness...");
    
    // Convert seed to bits
    let input_bits = encode_seed_to_bits(&seed_phrase);
    
    // Collect BP trace for proof
    let bp_trace = collect_bp_trace(&input_bits, &obf_prog.bp_matrices);
    
    // Serialize ObfProg for witness
    let obf_prog_bytes = serde_json::to_vec(&obf_prog)
        .map_err(|e| JsValue::from_str(&format!("Serialization error: {}", e)))?;
    
    let witness = ProofWitness {
        seed_phrase,
        obf_prog: obf_prog_bytes,
        bp_trace,
    };
    
    serde_wasm_bindgen::to_value(&witness)
        .map_err(|e| JsValue::from_str(&format!("Serialization error: {}", e)))
}

/// Batch evaluate multiple seed phrase guesses
///
/// More efficient than calling evaluate_seed repeatedly
#[wasm_bindgen]
pub fn batch_evaluate(obf_prog_js: JsValue, seeds_js: JsValue) -> Result<JsValue, JsValue> {
    let obf_prog: ObfuscatedProgram = serde_wasm_bindgen::from_value(obf_prog_js)
        .map_err(|e| JsValue::from_str(&format!("Invalid ObfProg: {}", e)))?;
    
    let seeds: Vec<[u16; 12]> = serde_wasm_bindgen::from_value(seeds_js)
        .map_err(|e| JsValue::from_str(&format!("Invalid seeds: {}", e)))?;
    
    console_log!("[honeypot-wasm] Batch evaluating {} seeds...", seeds.len());
    
    let mut results: Vec<(usize, bool)> = Vec::new();
    
    for (idx, seed) in seeds.iter().enumerate() {
        let input_bits = encode_seed_to_bits(seed);
        let output = evaluate_matrix_bp(&input_bits, &obf_prog.bp_matrices);
        
        if output == 1 {
            console_log!("[honeypot-wasm] FOUND at index {}!", idx);
            results.push((idx, true));
        }
    }
    
    serde_wasm_bindgen::to_value(&results)
        .map_err(|e| JsValue::from_str(&format!("Serialization error: {}", e)))
}

// ============================================================================
// Internal Functions
// ============================================================================

/// Encode 12 BIP-39 word indices to 128 input bits
fn encode_seed_to_bits(seed: &[u16; 12]) -> Vec<bool> {
    let mut bits = Vec::with_capacity(128);
    
    for (i, &word) in seed.iter().enumerate() {
        // Each word is 11 bits
        for j in 0..11 {
            if i * 11 + j >= 128 {
                break;
            }
            let bit = (word >> (10 - j)) & 1 == 1;
            bits.push(bit);
        }
    }
    
    // Pad to 128 if needed
    while bits.len() < 128 {
        bits.push(false);
    }
    
    bits
}

/// 5x5 matrix multiplication mod 251
fn matrix_mul(a: &[[u8; 5]; 5], b: &[[u8; 5]; 5]) -> [[u8; 5]; 5] {
    let mut result = [[0u8; 5]; 5];
    
    for i in 0..5 {
        for j in 0..5 {
            let mut sum: u16 = 0;
            for k in 0..5 {
                sum += (a[i][k] as u16) * (b[k][j] as u16);
            }
            result[i][j] = (sum % 251) as u8;
        }
    }
    
    result
}

/// Identity matrix
fn identity_matrix() -> [[u8; 5]; 5] {
    [
        [1, 0, 0, 0, 0],
        [0, 1, 0, 0, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0],
        [0, 0, 0, 0, 1],
    ]
}

/// Evaluate matrix branching program
fn evaluate_matrix_bp(input: &[bool], matrices: &[[[u8; 5]; 5]]) -> u64 {
    let mut result = identity_matrix();
    
    for (i, &bit) in input.iter().enumerate() {
        if i >= matrices.len() {
            break;
        }
        // In a real BP, we'd select between M0 and M1 based on bit
        // For simplicity, just multiply by the matrix
        if bit {
            result = matrix_mul(&result, &matrices[i]);
        }
    }
    
    // Check if result is identity (output 1) or not (output 0)
    if result == identity_matrix() { 1 } else { 0 }
}

/// Collect BP evaluation trace for proof witness
fn collect_bp_trace(input: &[bool], matrices: &[[[u8; 5]; 5]]) -> Vec<[[u8; 5]; 5]> {
    let mut trace = Vec::new();
    let mut result = identity_matrix();
    
    trace.push(result);
    
    for (i, &bit) in input.iter().enumerate() {
        if i >= matrices.len() {
            break;
        }
        if bit {
            result = matrix_mul(&result, &matrices[i]);
        }
        trace.push(result);
    }
    
    trace
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_matrix_mul() {
        let id = identity_matrix();
        let result = matrix_mul(&id, &id);
        assert_eq!(result, id);
    }
    
    #[test]
    fn test_encode_seed() {
        let seed: [u16; 12] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
        let bits = encode_seed_to_bits(&seed);
        assert_eq!(bits.len(), 128);
    }
}
