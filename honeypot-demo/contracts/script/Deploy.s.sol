// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import {Script, console2} from "forge-std/Script.sol";
import {SeedPhraseHoneypot} from "../src/HoneypotContract.sol";

interface IHonkVerifier {
    function verify(bytes calldata proof, bytes32[] calldata publicInputs) external view returns (bool);
}

contract DeployScript is Script {
    function run() external {
        uint256 deployerPrivateKey = vm.envOr("PRIVATE_KEY", uint256(0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80));
        
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
