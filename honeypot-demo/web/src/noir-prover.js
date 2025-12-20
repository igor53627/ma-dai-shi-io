/**
 * Noir zkSNARK Prover integration using bb.js
 * 
 * Uses UltraHonkBackend for proof generation and verification.
 */

import { UltraHonkBackend } from '@aztec/bb.js';
import { Noir } from '@noir-lang/noir_js';
import initNoirC from '@noir-lang/noirc_abi';
import initACVM from '@noir-lang/acvm_js';
import acvm from '@noir-lang/acvm_js/web/acvm_js_bg.wasm?url';
import noirc from '@noir-lang/noirc_abi/web/noirc_abi_wasm_bg.wasm?url';

let initialized = false;
let noir = null;
let backend = null;

/**
 * Initialize the Noir prover with circuit artifacts
 * @param {Object} circuit - Compiled circuit JSON
 */
export async function initProver(circuit) {
  if (!initialized) {
    // Initialize WASM modules using Vite's ?url import
    await Promise.all([
      initACVM(fetch(acvm)),
      initNoirC(fetch(noirc)),
    ]);
    initialized = true;
    console.log('[noir-prover] WASM modules initialized');
  }
  
  noir = new Noir(circuit);
  backend = new UltraHonkBackend(circuit.bytecode);
  
  console.log('[noir-prover] Initialized with circuit');
  return { noir, backend };
}

/**
 * Generate a zkSNARK proof for the given witness
 * @param {Object} witness - Noir witness object from generate_noir_witness
 * @returns {Object} - { proof, publicInputs }
 */
export async function generateProof(witness) {
  if (!noir || !backend) {
    throw new Error('Prover not initialized. Call initProver first.');
  }
  
  console.log('[noir-prover] Executing circuit...');
  const { witness: noirWitness } = await noir.execute(witness);
  
  console.log('[noir-prover] Generating proof...');
  const proof = await backend.generateProof(noirWitness);
  
  console.log('[noir-prover] Proof generated');
  return proof;
}

/**
 * Verify a proof
 * @param {Object} proof - Proof object from generateProof
 * @returns {boolean} - True if valid
 */
export async function verifyProof(proof) {
  if (!backend) {
    throw new Error('Prover not initialized. Call initProver first.');
  }
  
  console.log('[noir-prover] Verifying proof...');
  const isValid = await backend.verifyProof(proof);
  console.log(`[noir-prover] Proof is ${isValid ? 'valid' : 'invalid'}`);
  return isValid;
}

/**
 * Get the proof as hex bytes for smart contract submission
 * @param {Object} proof - Proof object
 * @returns {string} - Hex-encoded proof bytes
 */
export function proofToHex(proof) {
  const bytes = proof.proof;
  return '0x' + Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
}
