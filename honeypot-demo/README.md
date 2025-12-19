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
honeypot-noir/
├── circuits/           # Full circuit (128 BP steps, ~128k constraints)
├── circuits-medium/    # Medium circuit (16 BP steps, ~18k constraints) [OK]
├── circuits-minimal/   # Minimal test circuit (~19 constraints) [OK]
├── contracts/
│   ├── HoneypotContract.sol    # Main honeypot logic
│   └── HoneypotVerifier.sol    # Generated UltraHonk verifier
├── wasm/               # Ma-Dai-Shi WASM build
├── web/                # Browser UI
│   └── data/bip39-english.txt  # BIP-39 wordlist
└── scripts/            # Setup & test scripts
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
# Build WASM module
cd wasm
wasm-pack build --target web --out-dir ../web/pkg

# Serve the web app
cd ../web
python3 -m http.server 8080
# Open http://localhost:8080 in browser
```

The web UI lets you:
- Enter 12 BIP-39 words and evaluate against the obfuscated program
- Generate random seed phrases for testing  
- Batch brute-force (demo only - 2^128 entropy is infeasible)
- Generate zkSNARK proof when valid seed found

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
