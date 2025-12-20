# Ma-Dai-Shi Honeypot Demo (Noir + WASM)

Seed phrase honeypot using Ma-Dai-Shi iO with zkSNARK verification.

**Status:** [OK] Full proof flow working (nargo 1.0.0-beta.3 + bb 0.82.2)

## Architecture

```
+----------------------------------------------------------+
|                      Browser (WASM)                      |
|  +----------------+         +------------------------+   |
|  | Ma-Dai-Shi     |  -----> | Noir Prover (bb.js)    |   |
|  | Evaluator      |  found! | Generate zkSNARK       |   |
|  +----------------+         +-----------+------------+   |
+------------------------------------------|--------------+
                                           | proof
+------------------------------------------v--------------+
|                    Ethereum Mainnet                      |
|  +----------------------------------------------------+  |
|  | HoneypotContract.claim(proof) -> transfer funds    |  |
|  +----------------------------------------------------+  |
+----------------------------------------------------------+
```

## Structure

```
honeypot-demo/
├── circuits/           # Full circuit (128 BP steps, ~128k constraints)
├── circuits-medium/    # Medium circuit (16 BP steps, ~18k constraints) [OK]
├── circuits-minimal/   # Minimal test circuit (~19 constraints) [OK]
├── contracts/
│   ├── HoneypotContract.sol    # Main honeypot logic
│   └── HoneypotVerifier.sol    # Generated UltraHonk verifier
├── wasm/               # Ma-Dai-Shi WASM build
│   └── src/lib.rs              # evaluate_seed, generate_noir_witness, etc.
├── web/                # Browser UI
│   ├── data/
│   │   ├── bip39-english.txt   # BIP-39 wordlist (2048 words)
│   │   └── obf_prog.json       # Generated obfuscated program
│   ├── index.html              # Main honeypot UI
│   ├── protocol.html           # Protocol visualization
│   └── pkg/                    # WASM build output
└── scripts/
    ├── generate_obf_prog.py    # Generate ObfuscatedProgram JSON
    ├── generate_prover_toml.py # Generate Noir test inputs
    └── setup.sh                # Initial setup
```

## Quick Start

```bash
# Install compatible toolchain
noirup --version 1.0.0-beta.3
~/.bb/bbup  # Auto-detects nargo version -> bb 0.82.2

# Build medium circuit (recommended for testing)
cd circuits-medium
nargo compile
nargo test
nargo execute

# Generate proof
mkdir -p target/vk target/proof
bb write_vk -b target/honeypot_medium.json --output_path target/vk
bb prove -b target/honeypot_medium.json -w target/honeypot_medium.gz --output_path target/proof
bb verify -k target/vk/vk -p target/proof/proof  # "Proof verified successfully"

# Generate Solidity verifier
bb write_solidity_verifier -k target/vk/vk --output_path target/HoneypotVerifier.sol
```

## Web Demo

```bash
# Build WASM evaluator
cd wasm
wasm-pack build --target web --out-dir ../web/pkg

# Install dependencies and start dev server
cd ../web
npm install
npm run dev
# Open http://localhost:8080 in browser

# Or build for production
npm run build
# Serve dist/ folder
```

The web UI lets you:
- Enter 12 BIP-39 words and evaluate against the obfuscated program
- Generate random seed phrases for testing  
- Batch brute-force (demo only - 2^128 entropy is infeasible)
- Generate Noir witness when valid seed found (console output for CLI proving)

## WASM API

| Function | Description |
|----------|-------------|
| `evaluate_seed(obfProg, seedIndices)` | Evaluate seed phrase, returns `{is_valid, output, time_ms}` |
| `batch_evaluate(obfProg, seeds)` | Batch evaluation, returns array of valid indices |
| `generate_witness(obfProg, seed)` | Generate witness with BP trace (legacy) |
| `generate_noir_witness(obfProg, seed)` | Generate Noir-compatible witness JSON |
| `compute_program_hash(obfProg)` | Compute simple_hash matching Noir circuit |

## Hash Alignment

The `simple_hash` commitment scheme is consistent across all components:

```
Noir:   acc += arr[i * 25] * (i + 1) for i in 0..steps
WASM:   acc += mat[0][0] * (i + 1) for each matrix
Python: acc += mat[0][0] * (i + 1) for each matrix
```

For 16 identity matrices: `hash = 1*1 + 1*2 + ... + 1*16 = 136`

## Circuit Variants

| Circuit | BP Steps | Constraints | VK Generation | Proof Time | Use Case |
|---------|----------|-------------|---------------|------------|----------|
| minimal | N/A | 19 | <1s | <1s | Testing flow |
| medium | 16 | 18k | ~2s | ~3s | Development |
| full | 128 | 128k | ~5min | ~10min | Production |

## Version Compatibility

| Tool | Version | Notes |
|------|---------|-------|
| nargo | 1.0.0-beta.3 | Install via `noirup --version 1.0.0-beta.3` |
| bb | 0.82.2 | Auto-installed via `bbup` |
| Solidity | >=0.8.21 | For generated verifier |

## Related

- Issue: #59
- Main iO impl: `src/ma_dai_shi_io.rs`
- Paper: https://eprint.iacr.org/2025/307
