// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";
import {SeedPhraseHoneypot} from "../src/HoneypotContract.sol";

interface IHonkVerifier {
    function verify(bytes calldata proof, bytes32[] calldata publicInputs) external view returns (bool);
}

contract DeployScript is Script {
    // NOTE: Default key is Anvil/Hardhat test account #0 - ONLY for local development!
    // For production deployments, always set PRIVATE_KEY environment variable.
    uint256 constant ANVIL_DEFAULT_KEY = 0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80;
    
    function run() external {
        uint256 deployerPrivateKey = vm.envOr("PRIVATE_KEY", ANVIL_DEFAULT_KEY);
        
        // Warn if using default key on non-local chain
        if (deployerPrivateKey == ANVIL_DEFAULT_KEY && block.chainid != 31337) {
            console2.log("[WARN] Using default Anvil key on non-local chain!");
        }
        
        // Program hash: 136 (simple_hash for 16 identity matrices)
        bytes32 obfProgHash = bytes32(uint256(136));
        
        vm.startBroadcast(deployerPrivateKey);
        
        // Deploy verifier
        address verifier = deployCode("HoneypotVerifier.sol:HonkVerifier");
        console2.log("Verifier deployed at:", verifier);
        
        // Deploy honeypot with 0.1 ETH
        SeedPhraseHoneypot honeypot = new SeedPhraseHoneypot{value: 0.1 ether}(obfProgHash, verifier);
        console2.log("Honeypot deployed at:", address(honeypot));
        console2.log("Prize:", address(honeypot).balance);
        
        vm.stopBroadcast();
        
        console2.log("");
        console2.log("=== Deployment Complete ===");
        console2.log("Add to .env:");
        console2.log("VITE_HONEYPOT_ADDRESS=", address(honeypot));
    }
}
