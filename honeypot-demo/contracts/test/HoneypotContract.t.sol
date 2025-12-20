// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/HoneypotContract.sol";
import "../src/MockVerifier.sol";

contract SeedPhraseHoneypotTest is Test {
    SeedPhraseHoneypot public honeypot;
    MockVerifier public verifier;
    
    address public deployer = address(0x1);
    address public claimer = address(0x2);
    address public attacker = address(0x3);
    
    bytes32 public constant PROGRAM_HASH = bytes32(uint256(136)); // simple_hash for identity matrices
    uint256 public constant PRIZE_AMOUNT = 0.1 ether;

    function setUp() public {
        vm.deal(deployer, 10 ether);
        vm.deal(claimer, 1 ether);
        vm.deal(attacker, 1 ether);
        
        vm.startPrank(deployer);
        verifier = new MockVerifier();
        honeypot = new SeedPhraseHoneypot{value: PRIZE_AMOUNT}(PROGRAM_HASH, address(verifier));
        vm.stopPrank();
    }

    function test_DeploymentState() public view {
        assertEq(honeypot.obfProgHash(), PROGRAM_HASH);
        assertEq(address(honeypot.verifier()), address(verifier));
        assertEq(honeypot.claimed(), false);
        assertEq(honeypot.winner(), address(0));
        assertEq(honeypot.prize(), PRIZE_AMOUNT);
        assertTrue(honeypot.isActive());
    }

    function test_ClaimWithValidProof() public {
        bytes memory fakeProof = new bytes(200);
        
        uint256 claimerBalanceBefore = claimer.balance;
        
        vm.prank(claimer);
        honeypot.claim(fakeProof);
        
        assertTrue(honeypot.claimed());
        assertEq(honeypot.winner(), claimer);
        assertEq(honeypot.prize(), 0);
        assertFalse(honeypot.isActive());
        assertEq(claimer.balance, claimerBalanceBefore + PRIZE_AMOUNT);
    }

    function test_RevertDoubleClaimAttempt() public {
        bytes memory fakeProof = new bytes(200);
        
        vm.prank(claimer);
        honeypot.claim(fakeProof);
        
        vm.expectRevert("Already claimed");
        vm.prank(attacker);
        honeypot.claim(fakeProof);
    }

    function test_RevertInvalidProof() public {
        bytes memory shortProof = new bytes(50);
        
        vm.expectRevert("Invalid proof");
        vm.prank(attacker);
        honeypot.claim(shortProof);
    }

    function test_ReceiveAdditionalFunds() public {
        uint256 additionalFunds = 0.5 ether;
        
        vm.deal(address(this), additionalFunds);
        (bool sent,) = address(honeypot).call{value: additionalFunds}("");
        assertTrue(sent);
        
        assertEq(honeypot.prize(), PRIZE_AMOUNT + additionalFunds);
    }

    function test_RevertReceiveAfterClaimed() public {
        bytes memory fakeProof = new bytes(200);
        vm.prank(claimer);
        honeypot.claim(fakeProof);
        
        vm.deal(address(this), 0.1 ether);
        // Low-level call returns false on revert, doesn't bubble up
        (bool sent,) = address(honeypot).call{value: 0.1 ether}("");
        assertFalse(sent);
    }

    function test_InfoFunction() public view {
        (
            bytes32 progHash,
            uint256 prizeAmount,
            bool isClaimed,
            address winnerAddr,
            uint256 age
        ) = honeypot.info();
        
        assertEq(progHash, PROGRAM_HASH);
        assertEq(prizeAmount, PRIZE_AMOUNT);
        assertFalse(isClaimed);
        assertEq(winnerAddr, address(0));
        assertLe(age, 3600); // Age should be within 1 hour of deployment
    }

    function test_RevertZeroProgramHash() public {
        vm.expectRevert("Invalid program hash");
        vm.prank(deployer);
        new SeedPhraseHoneypot{value: 0.1 ether}(bytes32(0), address(verifier));
    }

    function test_RevertZeroVerifier() public {
        vm.expectRevert("Invalid verifier");
        vm.prank(deployer);
        new SeedPhraseHoneypot{value: 0.1 ether}(PROGRAM_HASH, address(0));
    }

    function test_RevertEOAVerifier() public {
        vm.expectRevert("Verifier has no code");
        vm.prank(deployer);
        new SeedPhraseHoneypot{value: 0.1 ether}(PROGRAM_HASH, address(0x999));
    }

    function test_RevertZeroFunding() public {
        vm.expectRevert("Must fund honeypot");
        vm.prank(deployer);
        new SeedPhraseHoneypot(PROGRAM_HASH, address(verifier));
    }
}

contract HoneypotFactoryTest is Test {
    HoneypotFactory public factory;
    MockVerifier public verifier;
    
    address public deployer = address(0x1);
    bytes32 public constant PROGRAM_HASH = bytes32(uint256(136));

    function setUp() public {
        vm.deal(deployer, 10 ether);
        
        vm.startPrank(deployer);
        verifier = new MockVerifier();
        factory = new HoneypotFactory(address(verifier));
        vm.stopPrank();
    }

    function test_FactoryDeployment() public view {
        assertEq(factory.verifier(), address(verifier));
        assertEq(factory.getHoneypots().length, 0);
        assertEq(factory.activeCount(), 0);
    }

    function test_CreateHoneypot() public {
        vm.prank(deployer);
        address honeypotAddr = factory.createHoneypot{value: 0.1 ether}(PROGRAM_HASH);
        
        assertEq(factory.getHoneypots().length, 1);
        assertEq(factory.honeypots(0), honeypotAddr);
        assertEq(factory.activeCount(), 1);
        
        SeedPhraseHoneypot honeypot = SeedPhraseHoneypot(payable(honeypotAddr));
        assertEq(honeypot.obfProgHash(), PROGRAM_HASH);
        assertEq(honeypot.prize(), 0.1 ether);
    }

    function test_CreateMultipleHoneypots() public {
        vm.startPrank(deployer);
        factory.createHoneypot{value: 0.1 ether}(PROGRAM_HASH);
        factory.createHoneypot{value: 0.2 ether}(bytes32(uint256(200)));
        factory.createHoneypot{value: 0.3 ether}(bytes32(uint256(300)));
        vm.stopPrank();
        
        assertEq(factory.getHoneypots().length, 3);
        assertEq(factory.activeCount(), 3);
    }

    function test_ActiveCountAfterClaim() public {
        vm.prank(deployer);
        address honeypotAddr = factory.createHoneypot{value: 0.1 ether}(PROGRAM_HASH);
        
        assertEq(factory.activeCount(), 1);
        
        bytes memory fakeProof = new bytes(200);
        vm.prank(deployer);
        SeedPhraseHoneypot(payable(honeypotAddr)).claim(fakeProof);
        
        assertEq(factory.activeCount(), 0);
    }

    function test_RevertFactoryZeroVerifier() public {
        vm.expectRevert("Invalid verifier");
        new HoneypotFactory(address(0));
    }

    function test_RevertFactoryEOAVerifier() public {
        vm.expectRevert("Verifier has no code");
        new HoneypotFactory(address(0x999));
    }
}
