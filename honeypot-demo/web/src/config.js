/**
 * Shared configuration for Ma-Dai-Shi Honeypot Web App
 * 
 * These values are used by both the app and tests.
 * Update .env file for different deployments.
 */

export const config = {
  // Tenderly Virtual Testnet RPC
  rpcUrl: import.meta.env.VITE_RPC_URL || 'https://virtual.sepolia.eu.rpc.tenderly.co/4d623b04-35fd-4fe7-8e76-6c2757f265ad',
  
  // Deployed contract addresses
  honeypotAddress: import.meta.env.VITE_HONEYPOT_ADDRESS || '0xCBf7fe54F7aEe6eD748e47094BD6E7286F3af276',
  verifierAddress: import.meta.env.VITE_VERIFIER_ADDRESS || '0x4cD6BA54F81213d27D650C750e27c234d8a3042B',
  
  // Chain configuration
  chainId: parseInt(import.meta.env.VITE_CHAIN_ID || '73571'),
  
  // Expected program hash (for demo with identity matrices)
  expectedProgramHash: 136,
};

export default config;
