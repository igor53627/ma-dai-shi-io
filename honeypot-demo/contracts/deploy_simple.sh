#!/bin/bash
RPC="https://virtual.sepolia.eu.rpc.tenderly.co/4d623b04-35fd-4fe7-8e76-6c2757f265ad"
PK="0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80"

# Deploy verifier
echo "Deploying HonkVerifier..."
RESULT=$( ~/.foundry/bin/forge create src/HoneypotVerifier.sol:HonkVerifier --rpc-url "$RPC" --private-key "$PK" --legacy 2>&1 )
VERIFIER=$(echo "$RESULT" | grep -oE '0x[a-fA-F0-9]{40}' | head -1)
echo "Verifier: $VERIFIER"

# Check if deployed
CODE=$(~/.foundry/bin/cast code "$VERIFIER" --rpc-url "$RPC" 2>/dev/null | head -c 10)
if [ "$CODE" != "0x" ] && [ -n "$CODE" ]; then
    echo "Verifier has code!"
else
    echo "Verifier has NO code - deployment failed"
    exit 1
fi

# Deploy honeypot
echo "Deploying SeedPhraseHoneypot..."
OBF_PROG_HASH="0x0000000000000000000000000000000000000000000000000000000000000088"
RESULT2=$( ~/.foundry/bin/forge create src/HoneypotContract.sol:SeedPhraseHoneypot --rpc-url "$RPC" --private-key "$PK" --legacy --constructor-args "$OBF_PROG_HASH" "$VERIFIER" --value 0.1ether 2>&1 )
HONEYPOT=$(echo "$RESULT2" | grep -oE '0x[a-fA-F0-9]{40}' | head -1)
echo "Honeypot: $HONEYPOT"

# Update .env
cat > ../web/.env << ENVEOF
VITE_RPC_URL=$RPC
VITE_HONEYPOT_ADDRESS=$HONEYPOT
VITE_CHAIN_ID=73571
ENVEOF

echo "Done! Check ../web/.env"
