/**
 * Ethereum integration using viem
 * 
 * Handles wallet connection and contract interaction.
 */

import { 
  createPublicClient, 
  createWalletClient, 
  custom, 
  http,
  parseEther,
  formatEther
} from 'viem';
import { sepolia } from 'viem/chains';
import { config } from './config.js';

// Contract ABI (minimal for honeypot)
const HONEYPOT_ABI = [
  {
    name: 'claim',
    type: 'function',
    stateMutability: 'nonpayable',
    inputs: [{ name: 'proof', type: 'bytes' }],
    outputs: [],
  },
  {
    name: 'claimed',
    type: 'function',
    stateMutability: 'view',
    inputs: [],
    outputs: [{ type: 'bool' }],
  },
  {
    name: 'obfProgHash',
    type: 'function',
    stateMutability: 'view',
    inputs: [],
    outputs: [{ type: 'bytes32' }],
  },
  {
    name: 'winner',
    type: 'function',
    stateMutability: 'view',
    inputs: [],
    outputs: [{ type: 'address' }],
  },
];

let publicClient = null;
let walletClient = null;
let account = null;
let contractAddress = config.honeypotAddress;

/**
 * Initialize the Ethereum client
 * @param {Object} options - { rpcUrl, contractAddress }
 */
export async function initEthereum(options = {}) {
  const rpcUrl = options.rpcUrl || config.rpcUrl;
  contractAddress = options.contractAddress || config.honeypotAddress;
  
  if (!rpcUrl) {
    console.log('[ethereum] No RPC URL configured, using browser provider');
  }
  
  // Create public client for reading
  publicClient = createPublicClient({
    chain: sepolia,
    transport: rpcUrl ? http(rpcUrl) : custom(window.ethereum),
  });
  
  console.log('[ethereum] Public client initialized');
  return publicClient;
}

/**
 * Connect wallet (MetaMask, etc.)
 * @returns {string} Connected account address
 */
export async function connectWallet() {
  if (!window.ethereum) {
    throw new Error('No wallet found. Please install MetaMask.');
  }
  
  // Request account access
  const accounts = await window.ethereum.request({ 
    method: 'eth_requestAccounts' 
  });
  
  if (accounts.length === 0) {
    throw new Error('No accounts found');
  }
  
  account = accounts[0];
  
  // Create wallet client for signing
  walletClient = createWalletClient({
    account,
    chain: sepolia,
    transport: custom(window.ethereum),
  });
  
  console.log(`[ethereum] Connected: ${account}`);
  return account;
}

/**
 * Get honeypot contract info
 * @returns {Object} { claimed, obfProgHash, balance }
 */
export async function getHoneypotInfo() {
  if (!publicClient || !contractAddress) {
    throw new Error('Ethereum not initialized or contract address not set');
  }
  
  const [claimed, obfProgHash, balance] = await Promise.all([
    publicClient.readContract({
      address: contractAddress,
      abi: HONEYPOT_ABI,
      functionName: 'claimed',
    }),
    publicClient.readContract({
      address: contractAddress,
      abi: HONEYPOT_ABI,
      functionName: 'obfProgHash',
    }),
    publicClient.getBalance({ address: contractAddress }),
  ]);
  
  return {
    claimed,
    obfProgHash,
    balance: formatEther(balance),
    balanceWei: balance,
  };
}

/**
 * Submit proof to claim the honeypot
 * @param {string} proofHex - Hex-encoded proof bytes
 * @returns {string} Transaction hash
 */
export async function claimHoneypot(proofHex) {
  if (!walletClient || !contractAddress) {
    throw new Error('Wallet not connected or contract address not set');
  }
  
  console.log('[ethereum] Submitting claim...');
  
  const hash = await walletClient.writeContract({
    address: contractAddress,
    abi: HONEYPOT_ABI,
    functionName: 'claim',
    args: [proofHex],
  });
  
  console.log(`[ethereum] Transaction submitted: ${hash}`);
  
  // Wait for confirmation
  const receipt = await publicClient.waitForTransactionReceipt({ hash });
  
  console.log(`[ethereum] Transaction confirmed in block ${receipt.blockNumber}`);
  return hash;
}

/**
 * Get connected account address
 */
export function getAccount() {
  return account;
}

/**
 * Check if wallet is connected
 */
export function isConnected() {
  return account !== null;
}

/**
 * Set contract address at runtime
 */
export function setContractAddress(address) {
  contractAddress = address;
}
