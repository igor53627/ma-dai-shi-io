#!/bin/bash
# Deploy honeypot contracts to Tenderly Virtual Testnet
# Usage: ./deploy.sh

set -e

# Load secrets
source ~/.zsh_secrets

# Configuration (do not commit actual values)
RPC_URL="${TENDERLY_VIRTUAL_RPC:-https://virtual.sepolia.eu.rpc.tenderly.co/4d623b04-35fd-4fe7-8e76-6c2757f265ad}"
PRIVATE_KEY="${TENDERLY_PRIVATE_KEY:-0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80}"  # Anvil default

# Program hash (simple_hash = 136 for 16 identity matrices)
# Convert to bytes32: pad to 32 bytes
OBF_PROG_HASH="0x0000000000000000000000000000000000000000000000000000000000000088"  # 136 in hex

echo "Deploying to: $RPC_URL"
echo "Program hash: $OBF_PROG_HASH"

cd "$(dirname "$0")"

# Deploy verifier first (using the generated HoneypotVerifier.sol)
echo "[1/3] Deploying HonkVerifier..."
VERIFIER_ADDR=$(~/.foundry/bin/forge create HoneypotVerifier.sol:HonkVerifier \
  --rpc-url "$RPC_URL" \
  --private-key "$PRIVATE_KEY" \
  --json 2>/dev/null | jq -r '.deployedTo')

echo "Verifier deployed at: $VERIFIER_ADDR"

# Deploy honeypot with 0.1 ETH prize
echo "[2/3] Deploying SeedPhraseHoneypot..."
HONEYPOT_ADDR=$(~/.foundry/bin/forge create HoneypotContract.sol:SeedPhraseHoneypot \
  --rpc-url "$RPC_URL" \
  --private-key "$PRIVATE_KEY" \
  --constructor-args "$OBF_PROG_HASH" "$VERIFIER_ADDR" \
  --value 0.1ether \
  --json 2>/dev/null | jq -r '.deployedTo')

echo "Honeypot deployed at: $HONEYPOT_ADDR"

# Verify deployment
echo "[3/3] Verifying deployment..."
PRIZE=$(~/.foundry/bin/cast call "$HONEYPOT_ADDR" "prize()(uint256)" --rpc-url "$RPC_URL")
echo "Prize: $PRIZE wei"

echo ""
echo "=== Deployment Complete ==="
echo "Verifier:  $VERIFIER_ADDR"
echo "Honeypot:  $HONEYPOT_ADDR"
echo "RPC URL:   $RPC_URL"
echo ""
echo "Add to .env:"
echo "VITE_RPC_URL=$RPC_URL"
echo "VITE_HONEYPOT_ADDRESS=$HONEYPOT_ADDR"
echo "VITE_CHAIN_ID=73571"
