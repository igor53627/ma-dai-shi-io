# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).

## [Unreleased]

### Added
- Initial release extracted from circuit-mixing-research
- Core Ma-Dai-Shi iO implementation (`src/lib.rs`)
- Honeypot demo with Noir circuits, Solidity contracts, WASM evaluator
- Interactive protocol visualization (`honeypot-demo/web/protocol.html`)
- BIP-39 seed phrase support (2048 word wordlist)

### Features
- Quasi-linear Õ(N) obfuscation (N = circuit size + proof size)
- Padding to fixed topology with routing networks
- LiO (Local iO) with SEH + FHE
- Browser-based evaluation via WASM
- zkSNARK proof generation for on-chain verification
