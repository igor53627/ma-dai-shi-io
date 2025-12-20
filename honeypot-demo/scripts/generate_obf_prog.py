#!/usr/bin/env python3
"""Generate ObfuscatedProgram JSON for web UI.

Creates a real obfuscated program that accepts a specific secret seed phrase.
For the demo, we use identity matrices which accept any seed with all-zero bits
(i.e., seed phrase indices that are all 0).
"""

import json
import hashlib
import argparse


def generate_identity_matrix():
    """5x5 identity matrix."""
    return [
        [1, 0, 0, 0, 0],
        [0, 1, 0, 0, 0],
        [0, 0, 1, 0, 0],
        [0, 0, 0, 1, 0],
        [0, 0, 0, 0, 1]
    ]


def simple_hash(matrices):
    """Compute simple_hash matching Noir circuit.
    
    For medium (16 steps): acc += mat[0][0] * (i+1) for each matrix
    """
    acc = 0
    for i, mat in enumerate(matrices):
        acc += mat[0][0] * (i + 1)
    return acc


def generate_obf_prog(steps: int = 16) -> dict:
    """Generate ObfuscatedProgram for web UI."""
    matrices = [generate_identity_matrix() for _ in range(steps)]
    
    prog_hash = simple_hash(matrices)
    
    hash_bytes = list(prog_hash.to_bytes(32, 'big'))
    
    return {
        "hash": hash_bytes,
        "bp_matrices": matrices,
        "input_bits": steps,
        "simple_hash": prog_hash
    }


def main():
    parser = argparse.ArgumentParser(description="Generate ObfuscatedProgram JSON")
    parser.add_argument("--steps", type=int, default=16, help="Number of BP steps (16 or 128)")
    parser.add_argument("--output", type=str, default="../web/data/obf_prog.json", help="Output path")
    args = parser.parse_args()
    
    prog = generate_obf_prog(args.steps)
    
    with open(args.output, 'w') as f:
        json.dump(prog, f, indent=2)
    
    print(f"Generated ObfuscatedProgram ({args.steps} steps)")
    print(f"  simple_hash: {prog['simple_hash']}")
    print(f"  Saved to: {args.output}")
    print(f"  Valid seed: all zeros (word indices 0,0,0,0,0,0,0,0,0,0,0,0)")


if __name__ == "__main__":
    main()
