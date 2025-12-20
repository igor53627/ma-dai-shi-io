// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title Mock Verifier for Demo
/// @notice Always returns true for valid proofs (demo only!)
contract MockVerifier {
    function verify(bytes calldata proof, bytes32[] calldata publicInputs) external pure returns (bool) {
        // In production, this would verify the ZK proof
        // For demo, check proof length matches UltraHonk format (~4KB)
        return proof.length > 100;
    }
}
