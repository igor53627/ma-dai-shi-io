/**
 * Ma-Dai-Shi Honeypot Web App
 * 
 * Main application logic for the honeypot demo.
 */

import init, { 
  evaluate_seed, 
  batch_evaluate, 
  generate_witness, 
  generate_noir_witness, 
  compute_program_hash 
} from '../pkg/honeypot_wasm.js';

import { initProver, generateProof, verifyProof, proofToHex } from './noir-prover.js';
import { 
  initEthereum, 
  connectWallet, 
  getHoneypotInfo, 
  claimHoneypot, 
  isConnected, 
  getAccount,
  setContractAddress 
} from './ethereum.js';

// State
let wasmReady = false;
let proverReady = false;
let ethereumReady = false;
let obfProg = null;
let circuit = null;
let batchRunning = false;
let foundSeed = null;
let bip39Wordlist = [];
let wordToIndex = new Map();
let lastProofHex = null;

// DOM helpers
function $(id) { return document.getElementById(id); }

function showStatus(id, type, message) {
  const el = $(id);
  el.style.display = 'block';
  el.className = `status ${type}`;
  el.textContent = message;
}

function log(message, type = '') {
  const el = $('log');
  const entry = document.createElement('div');
  entry.className = `log-entry ${type}`;
  entry.textContent = `[${new Date().toLocaleTimeString()}] ${message}`;
  el.appendChild(entry);
  el.scrollTop = el.scrollHeight;
  console.log(`[honeypot] ${message}`);
}

// Initialization
export async function initialize() {
  log('Initializing WASM module...');
  
  try {
    await init();
    wasmReady = true;
    log('WASM ready', 'success');
    
    // Load wordlist and honeypot info in parallel
    await Promise.all([
      loadWordlist(),
      loadHoneypotInfo(),
      loadCircuit(),
    ]);
    
    // Initialize Ethereum (optional, won't fail if no provider)
    try {
      await initEthereum();
      ethereumReady = true;
      log('Ethereum ready');
    } catch (e) {
      log(`Ethereum init skipped: ${e.message}`);
    }
    
    $('tryBtn').disabled = false;
    $('batchBtn').disabled = false;
  } catch (e) {
    log(`Initialization failed: ${e}`, 'error');
    throw e;
  }
}

async function loadWordlist() {
  const resp = await fetch('./data/bip39-english.txt');
  const text = await resp.text();
  bip39Wordlist = text.trim().split('\n').map(w => w.trim().toLowerCase());
  
  if (bip39Wordlist.length !== 2048) {
    log(`[WARN] Wordlist has ${bip39Wordlist.length} words, expected 2048`, 'error');
  }
  
  bip39Wordlist.forEach((word, idx) => wordToIndex.set(word, idx));
  log(`Loaded ${bip39Wordlist.length} BIP-39 words`);
}

async function loadHoneypotInfo() {
  try {
    const resp = await fetch('./data/obf_prog.json');
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    obfProg = await resp.json();
    
    const hash = obfProg.simple_hash || 'unknown';
    $('progHash').textContent = 
      `Program hash: ${hash} (simple_hash, ${obfProg.bp_matrices.length} steps)`;
    
    log(`Loaded ObfProg: ${obfProg.bp_matrices.length} matrices, hash=${hash}`);
  } catch (e) {
    log(`Failed to load obf_prog.json: ${e}, using mock`, 'error');
    obfProg = generateMockObfProg();
  }
  
  // Demo values (in production, fetch from contract)
  $('prize').textContent = '1.337 ETH';
  $('contract').textContent = 'Contract: 0x1234...5678 (Tenderly fork)';
  
  log('Loaded honeypot info');
}

async function loadCircuit() {
  try {
    const resp = await fetch('./data/honeypot_medium.json');
    if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
    circuit = await resp.json();
    
    log('Loading Noir prover...');
    await initProver(circuit);
    proverReady = true;
    log('Noir prover ready', 'success');
  } catch (e) {
    log(`Failed to load circuit: ${e}`, 'error');
    log('Proof generation will be unavailable', 'error');
  }
}

function generateMockObfProg() {
  const matrices = [];
  for (let i = 0; i < 16; i++) {
    const m = [];
    for (let r = 0; r < 5; r++) {
      const row = [];
      for (let c = 0; c < 5; c++) {
        row.push(r === c ? 1 : 0);
      }
      m.push(row);
    }
    matrices.push(m);
  }
  return {
    hash: new Array(32).fill(0),
    bp_matrices: matrices,
    input_bits: 16,
    simple_hash: 136
  };
}

// Try single seed
export async function trySeed() {
  if (!wasmReady) {
    log('WASM not ready', 'error');
    return;
  }
  
  const input = $('seedInput').value.trim();
  const words = input.split(/\s+/);
  
  if (words.length !== 12) {
    showStatus('tryStatus', 'error', 'Need exactly 12 words');
    return;
  }
  
  // Convert words to BIP-39 indices
  const indices = [];
  for (const word of words) {
    const idx = wordToIndex.get(word.toLowerCase());
    if (idx === undefined) {
      showStatus('tryStatus', 'error', `Unknown word: "${word}"`);
      return;
    }
    indices.push(idx);
  }
  
  log(`Evaluating: ${words.slice(0, 3).join(' ')}...`);
  showStatus('tryStatus', 'loading', 'Evaluating...');
  
  try {
    const result = await evaluate_seed(obfProg, indices);
    
    if (result.is_valid) {
      showStatus('tryStatus', 'success', 
        `[OK] VALID SEED FOUND! (${result.time_ms.toFixed(1)}ms)`);
      log('FOUND VALID SEED!', 'success');
      foundSeed = indices;
      $('claimCard').style.display = 'block';
    } else {
      showStatus('tryStatus', 'error', 
        `Invalid (output=${result.output}, ${result.time_ms.toFixed(1)}ms)`);
    }
  } catch (e) {
    showStatus('tryStatus', 'error', `Error: ${e}`);
    log(`Error: ${e}`, 'error');
  }
}

// Random seed
export function randomSeed() {
  if (bip39Wordlist.length === 0) {
    log('Wordlist not loaded yet', 'error');
    return;
  }
  const words = [];
  for (let i = 0; i < 12; i++) {
    words.push(bip39Wordlist[Math.floor(Math.random() * bip39Wordlist.length)]);
  }
  $('seedInput').value = words.join(' ');
}

// Batch brute force
export async function startBatch() {
  if (!wasmReady || batchRunning) return;
  
  batchRunning = true;
  const batchSize = parseInt($('batchSize').value);
  let index = parseInt($('startIndex').value);
  let attempts = 0;
  const startTime = Date.now();
  
  log(`Starting batch from index ${index}`);
  
  while (batchRunning) {
    const seeds = [];
    for (let i = 0; i < batchSize; i++) {
      seeds.push(indexToSeed(index + i));
    }
    
    try {
      const results = await batch_evaluate(obfProg, seeds);
      
      if (results.length > 0) {
        const [foundIdx, _] = results[0];
        foundSeed = seeds[foundIdx];
        log(`FOUND at index ${index + foundIdx}!`, 'success');
        $('claimCard').style.display = 'block';
        batchRunning = false;
        break;
      }
    } catch (e) {
      log(`Batch error: ${e}`, 'error');
    }
    
    index += batchSize;
    attempts += batchSize;
    
    const elapsed = (Date.now() - startTime) / 1000;
    const speed = Math.round(attempts / elapsed);
    $('attempts').textContent = attempts.toLocaleString();
    $('speed').textContent = speed.toLocaleString();
    
    const progress = Math.min(100, (attempts / 1000000) * 100);
    $('progressBar').style.width = `${progress}%`;
    
    await new Promise(r => setTimeout(r, 0));
  }
}

export function stopBatch() {
  batchRunning = false;
  log('Batch stopped');
}

function indexToSeed(index) {
  const seed = [];
  let n = BigInt(index);
  for (let i = 0; i < 12; i++) {
    seed.push(Number(n % 2048n));
    n = n / 2048n;
  }
  return seed;
}

// Claim prize - generate proof and submit to contract
export async function claimPrize() {
  if (!foundSeed) return;
  
  $('claimBtn').disabled = true;
  
  try {
    // Step 1: Generate Noir witness from WASM
    log('Generating Noir witness...');
    const noirWitness = await generate_noir_witness(obfProg, foundSeed);
    log(`Noir witness generated (hash: ${noirWitness.obf_prog_hash})`);
    
    if (!proverReady) {
      log('Prover not ready - outputting witness for CLI proving', 'error');
      console.log('Noir witness:', JSON.stringify(noirWitness, null, 2));
      showStatus('claimStatus', 'error', 'Prover not ready. Check console for witness.');
      $('claimBtn').disabled = false;
      return;
    }
    
    // Step 2: Generate proof with bb.js
    log('Generating zkSNARK proof (this may take a moment)...');
    showStatus('claimStatus', 'loading', 'Generating proof...');
    
    // Convert witness to Noir input format
    const inputs = {
      obf_prog_hash: noirWitness.obf_prog_hash,
      evaluation_output: noirWitness.evaluation_output,
      seed_phrase: noirWitness.seed_phrase,
      bp_matrices_flat: noirWitness.bp_matrices_flat,
    };
    
    const proof = await generateProof(inputs);
    log('Proof generated!', 'success');
    
    // Step 3: Verify locally
    log('Verifying proof locally...');
    const isValid = await verifyProof(proof);
    
    if (!isValid) {
      showStatus('claimStatus', 'error', 'Proof verification failed locally');
      $('claimBtn').disabled = false;
      return;
    }
    
    log('Proof verified locally', 'success');
    
    // Step 4: Get proof bytes for contract
    lastProofHex = proofToHex(proof);
    console.log('Proof hex:', lastProofHex);
    
    // Step 5: Submit to contract if connected
    if (isConnected()) {
      await submitToContract();
    } else {
      showStatus('claimStatus', 'success', 'Proof ready! Click "Connect Wallet" to claim.');
      log('Proof ready - connect wallet to submit', 'success');
    }
    
  } catch (e) {
    log(`Proof generation failed: ${e}`, 'error');
    showStatus('claimStatus', 'error', `Error: ${e.message}`);
    console.error(e);
  }
  
  $('claimBtn').disabled = false;
}

// Submit proof to contract
async function submitToContract() {
  if (!lastProofHex) {
    log('No proof available', 'error');
    return;
  }
  
  try {
    log('Submitting to contract...');
    showStatus('claimStatus', 'loading', 'Submitting transaction...');
    
    const txHash = await claimHoneypot(lastProofHex);
    
    showStatus('claimStatus', 'success', `Claimed! TX: ${txHash.slice(0, 10)}...`);
    log(`Transaction confirmed: ${txHash}`, 'success');
  } catch (e) {
    log(`Transaction failed: ${e.message}`, 'error');
    showStatus('claimStatus', 'error', `TX failed: ${e.message}`);
  }
}

// Connect wallet button handler
export async function handleConnectWallet() {
  try {
    log('Connecting wallet...');
    const account = await connectWallet();
    log(`Connected: ${account.slice(0, 6)}...${account.slice(-4)}`, 'success');
    
    // Update UI
    const btn = $('connectWalletBtn');
    if (btn) {
      btn.textContent = `${account.slice(0, 6)}...${account.slice(-4)}`;
      btn.disabled = true;
    }
    
    // If we have a proof ready, submit it
    if (lastProofHex) {
      await submitToContract();
    }
  } catch (e) {
    log(`Wallet connection failed: ${e.message}`, 'error');
  }
}

// Code viewer
let currentTab = 'json';

export function toggleCode() {
  const card = $('codeCard');
  card.style.display = card.style.display === 'none' ? 'block' : 'none';
  if (card.style.display === 'block') {
    updateCodeView();
  }
}

export function showTab(tab) {
  currentTab = tab;
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  event.target.classList.add('active');
  updateCodeView();
}

function updateCodeView() {
  if (!obfProg) return;
  
  const el = $('codeContent');
  let code = '';
  
  if (currentTab === 'json') {
    code = formatJson(obfProg);
  } else if (currentTab === 'rust') {
    code = formatRust(obfProg);
  } else if (currentTab === 'matrices') {
    code = formatMatrices(obfProg);
  }
  
  el.innerHTML = `<code>${code}</code>`;
  
  const stats = `${obfProg.bp_matrices.length} BP steps | 5x5 matrices | Field: GF(251)`;
  $('codeStats').textContent = stats;
}

function formatJson(prog) {
  const preview = {
    hash: '0x' + prog.hash.map(b => b.toString(16).padStart(2, '0')).join(''),
    input_bits: prog.input_bits,
    bp_matrices: `[${prog.bp_matrices.length} matrices...]`,
    bp_matrices_preview: prog.bp_matrices.slice(0, 2)
  };
  return syntaxHighlight(JSON.stringify(preview, null, 2));
}

function formatRust(prog) {
  return `<span class="comment">// Ma-Dai-Shi Obfuscated Program</span>
<span class="keyword">pub struct</span> <span class="type">ObfuscatedProgram</span> {
    <span class="comment">/// Program commitment hash</span>
    <span class="keyword">pub</span> <span class="property">hash</span>: [<span class="type">u8</span>; <span class="number">32</span>],
    
    <span class="comment">/// Matrix branching program (${prog.bp_matrices.length} steps)</span>
    <span class="keyword">pub</span> <span class="property">bp_matrices</span>: <span class="type">Vec</span>&lt;[[<span class="type">u8</span>; <span class="number">5</span>]; <span class="number">5</span>]&gt;,
    
    <span class="comment">/// Input size in bits</span>
    <span class="keyword">pub</span> <span class="property">input_bits</span>: <span class="type">usize</span>,  <span class="comment">// ${prog.input_bits}</span>
}

<span class="comment">// Evaluation: multiply matrices based on input bits</span>
<span class="comment">// Output 1 if result == Identity, else 0</span>
<span class="keyword">fn</span> <span class="property">evaluate</span>(prog: &<span class="type">ObfuscatedProgram</span>, input: &[<span class="type">bool</span>]) -> <span class="type">u64</span> {
    <span class="keyword">let mut</span> result = <span class="property">identity_matrix</span>();
    <span class="keyword">for</span> (i, &bit) <span class="keyword">in</span> input.iter().enumerate() {
        <span class="keyword">if</span> bit {
            result = <span class="property">matrix_mul</span>(&result, &prog.bp_matrices[i]);
        }
    }
    <span class="keyword">if</span> result == <span class="property">identity_matrix</span>() { <span class="number">1</span> } <span class="keyword">else</span> { <span class="number">0</span> }
}`;
}

function formatMatrices(prog) {
  let output = `<span class="comment">// Branching Program Matrices (first 4 of ${prog.bp_matrices.length})</span>\n`;
  output += `<span class="comment">// Field: GF(251), Dimension: 5x5</span>\n\n`;
  
  for (let i = 0; i < Math.min(4, prog.bp_matrices.length); i++) {
    output += `<span class="property">M[${i}]</span> = [\n`;
    for (let r = 0; r < 5; r++) {
      const row = prog.bp_matrices[i][r].map(v => 
        `<span class="number">${v.toString().padStart(3)}</span>`
      ).join(', ');
      output += `  [${row}],\n`;
    }
    output += `]\n\n`;
  }
  
  if (prog.bp_matrices.length > 4) {
    output += `<span class="comment">// ... ${prog.bp_matrices.length - 4} more matrices</span>\n`;
  }
  
  return output;
}

function syntaxHighlight(json) {
  return json
    .replace(/(".*?")/g, '<span class="string">$1</span>')
    .replace(/\b(\d+)\b/g, '<span class="number">$1</span>')
    .replace(/\b(true|false|null)\b/g, '<span class="keyword">$1</span>');
}

// Export for global access
window.trySeed = trySeed;
window.randomSeed = randomSeed;
window.startBatch = startBatch;
window.stopBatch = stopBatch;
window.claimPrize = claimPrize;
window.toggleCode = toggleCode;
window.showTab = showTab;
window.handleConnectWallet = handleConnectWallet;

// Auto-initialize
initialize().catch(e => log(`Init error: ${e}`, 'error'));
