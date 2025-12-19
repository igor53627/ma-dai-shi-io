# Ma-Dai-Shi iO

Quasi-linear indistinguishability obfuscation (iO).

Implementation of the construction from ["Quasi-Linear Indistinguishability Obfuscation via Mathematical Proofs of Equivalence and Applications"](https://eprint.iacr.org/2025/307) (Ma, Dai, Shi 2025).

## What is iO?

**Indistinguishability Obfuscation** transforms a program into an equivalent program that:
- Computes the exact same function
- Reveals nothing about its implementation
- Cannot be reverse-engineered to extract secrets

If two circuits compute the same function, their obfuscations are computationally indistinguishable.

## Key Features

- **Quasi-linear complexity**: Õ(N) obfuscation time and program size (N = circuit + proof size)
- **LWE-based security**: Based on LWE, sub-exponential OWF, and iO for small circuits
- **Practical for crypto**: Enables seed phrase honeypots, private smart contracts, etc.

## Repository Structure

```
ma-dai-shi-io/
├── src/lib.rs           # Core iO implementation
├── examples/            # Integration tests
└── honeypot-demo/       # Full demo application
    ├── circuits-medium/ # Noir zkSNARK circuits
    ├── contracts/       # Solidity verifier contracts
    ├── wasm/           # Browser-based evaluator
    └── web/            # Interactive demo UI
```

## Quick Start

### Rust Library

```rust
use ma_dai_shi_io::{MaDaiShiIO, MaDaiShiParams};

// Create obfuscator
let params = MaDaiShiParams::default();
let io = MaDaiShiIO::new(params);

// Obfuscate a circuit
let obf_prog = io.obfuscate(&circuit, &equivalence_proof)?;

// Evaluate (same result as original circuit)
let output = obf_prog.evaluate(&input);
```

### Honeypot Demo

```bash
# Build WASM evaluator
cd honeypot-demo/wasm
wasm-pack build --target web --out-dir ../web/pkg

# Serve the demo
cd ../web
python3 -m http.server 8080
# Open http://localhost:8080
```

The demo lets you:
- Try seed phrase guesses against an obfuscated validator
- See the protocol visualization explaining how iO works
- Generate zkSNARK proofs to claim prizes on-chain

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    Ma-Dai-Shi Quasi-Linear iO                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   Circuit C + Equivalence Proof π                               │
│              │                                                  │
│              ▼                                                  │
│   Pad to fixed topology (routing networks)                      │
│              │                                                  │
│              ▼                                                  │
│   LiO (local iO with SEH + FHE)                                │
│              │                                                  │
│              ▼                                                  │
│   ObfuscatedProgram                                             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Complexity Comparison

| Approach | Obfuscation Time | Program Size | Security |
|----------|------------------|--------------|----------|
| Naive (truth table) | O(2^n) | O(2^n) | None |
| Prior polynomial iO | O(n^c) large c | O(n^c) | LWE + assumptions |
| **Ma-Dai-Shi iO** | **Õ(N)** | **Õ(N)** | **LWE + OWF + small iO** |

## Honeypot Use Case

The honeypot demo shows a practical application:

1. **Setup**: Obfuscate a seed phrase validator, deploy with ETH prize
2. **Challenge**: Users try guesses in-browser (WASM evaluation)
3. **Claim**: Valid seed generates zkSNARK proof, smart contract verifies and transfers prize

**Double-layer privacy**:
- iO hides *how* the validator works (can't extract seed from program)
- zkSNARK hides *which* seed was found (contract only sees proof)

## Development

```bash
# Run tests
cargo test

# Build library
cargo build --release

# Run integration example
cargo run --example integration_test
```

## References

- [Ma-Dai-Shi 2025 Paper](https://eprint.iacr.org/2025/307)
- [Noir Language](https://noir-lang.org/) - zkSNARK DSL
- [BIP-39](https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki) - Mnemonic seed phrases

## License

MIT
