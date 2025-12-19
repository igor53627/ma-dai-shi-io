// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/// @title Ma-Dai-Shi Seed Phrase Honeypot
/// @notice Hide a 12-word seed phrase with iO, verify claims via zkSNARK
/// @dev Issue #59: https://github.com/igor53627/circuit-mixing-research/issues/59

interface IUltraVerifier {
    function verify(bytes calldata proof, bytes32[] calldata publicInputs) external view returns (bool);
}

contract SeedPhraseHoneypot {
    // ========================================================================
    // State
    // ========================================================================
    
    /// @notice Hash of the Ma-Dai-Shi obfuscated program
    bytes32 public immutable obfProgHash;
    
    /// @notice Noir UltraPlonk verifier contract
    IUltraVerifier public immutable verifier;
    
    /// @notice Whether the honeypot has been claimed
    bool public claimed;
    
    /// @notice Winner address (if claimed)
    address public winner;
    
    /// @notice Timestamp when honeypot was deployed
    uint256 public immutable deployedAt;
    
    // ========================================================================
    // Events
    // ========================================================================
    
    event HoneypotCreated(bytes32 indexed obfProgHash, uint256 prize);
    event HoneypotClaimed(address indexed winner, uint256 prize);
    event AttemptFailed(address indexed attacker);
    
    // ========================================================================
    // Constructor
    // ========================================================================
    
    /// @notice Create honeypot with obfuscated seed phrase validator
    /// @param _obfProgHash Keccak256 hash of serialized Ma-Dai-Shi ObfProg
    /// @param _verifier Address of deployed Noir UltraPlonk verifier
    constructor(bytes32 _obfProgHash, address _verifier) payable {
        require(_obfProgHash != bytes32(0), "Invalid program hash");
        require(_verifier != address(0), "Invalid verifier");
        require(msg.value > 0, "Must fund honeypot");
        
        obfProgHash = _obfProgHash;
        verifier = IUltraVerifier(_verifier);
        deployedAt = block.timestamp;
        
        emit HoneypotCreated(_obfProgHash, msg.value);
    }
    
    // ========================================================================
    // Claim
    // ========================================================================
    
    /// @notice Claim the honeypot by proving you know the seed phrase
    /// @param proof The zkSNARK proof from Noir prover
    /// @dev Proof verifies: "I know seed s.t. ObfProg(seed) = 1"
    function claim(bytes calldata proof) external {
        require(!claimed, "Already claimed");
        
        // Build public inputs array for verifier
        // [0] = obfProgHash (as Field)
        // [1] = evaluation_output = 1 (valid seed found)
        bytes32[] memory publicInputs = new bytes32[](2);
        publicInputs[0] = obfProgHash;
        publicInputs[1] = bytes32(uint256(1)); // output must be 1
        
        // Verify the proof
        bool valid = verifier.verify(proof, publicInputs);
        
        if (!valid) {
            emit AttemptFailed(msg.sender);
            revert("Invalid proof");
        }
        
        // Success! Transfer prize
        claimed = true;
        winner = msg.sender;
        
        uint256 prize = address(this).balance;
        (bool sent, ) = payable(msg.sender).call{value: prize}("");
        require(sent, "Transfer failed");
        
        emit HoneypotClaimed(msg.sender, prize);
    }
    
    // ========================================================================
    // View Functions
    // ========================================================================
    
    /// @notice Get current prize amount
    function prize() external view returns (uint256) {
        return address(this).balance;
    }
    
    /// @notice Check if honeypot is still active
    function isActive() external view returns (bool) {
        return !claimed && address(this).balance > 0;
    }
    
    /// @notice Get honeypot info
    function info() external view returns (
        bytes32 progHash,
        uint256 prizeAmount,
        bool isClaimed,
        address winnerAddr,
        uint256 age
    ) {
        return (
            obfProgHash,
            address(this).balance,
            claimed,
            winner,
            block.timestamp - deployedAt
        );
    }
    
    // ========================================================================
    // Receive
    // ========================================================================
    
    /// @notice Allow adding more funds to the honeypot
    receive() external payable {
        require(!claimed, "Already claimed");
    }
}

/// @title Honeypot Factory
/// @notice Deploy multiple honeypots with different seed phrases
contract HoneypotFactory {
    event HoneypotDeployed(address indexed honeypot, bytes32 indexed obfProgHash, uint256 prize);
    
    address public immutable verifier;
    address[] public honeypots;
    
    constructor(address _verifier) {
        verifier = _verifier;
    }
    
    function createHoneypot(bytes32 obfProgHash) external payable returns (address) {
        SeedPhraseHoneypot honeypot = new SeedPhraseHoneypot{value: msg.value}(
            obfProgHash,
            verifier
        );
        
        honeypots.push(address(honeypot));
        emit HoneypotDeployed(address(honeypot), obfProgHash, msg.value);
        
        return address(honeypot);
    }
    
    function getHoneypots() external view returns (address[] memory) {
        return honeypots;
    }
    
    function activeCount() external view returns (uint256 count) {
        for (uint256 i = 0; i < honeypots.length; i++) {
            if (SeedPhraseHoneypot(payable(honeypots[i])).isActive()) {
                count++;
            }
        }
    }
}
