import { test, expect } from '@playwright/test';

// Configuration - must match honeypot-demo/web/src/config.js and .env
// These are duplicated here since Playwright tests run in Node, not browser
const RPC_URL = process.env.VITE_RPC_URL || 'https://virtual.sepolia.eu.rpc.tenderly.co/4d623b04-35fd-4fe7-8e76-6c2757f265ad';
const HONEYPOT_ADDRESS = process.env.VITE_HONEYPOT_ADDRESS || '0xCBf7fe54F7aEe6eD748e47094BD6E7286F3af276';

// NOTE: These tests are written for the demo obf_prog (identity matrices).
// When switching to the real branching program, update expectations for validity.

test.describe('Ma-Dai-Shi Honeypot E2E', () => {
  
  test.beforeEach(async ({ page }) => {
    page.on('console', msg => console.log(`[browser] ${msg.text()}`));
    page.on('pageerror', err => console.error(`[browser error] ${err.message}`));
  });

  test('1. Page loads and WASM initializes', async ({ page }) => {
    await page.goto('/');
    
    // Wait for WASM to initialize
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });
    await expect(page.locator('#log')).toContainText('Loaded 2048 BIP-39 words');
    await expect(page.locator('#log')).toContainText('Loaded ObfProg');
    
    // Check honeypot info displayed (flexible match for program hash)
    await expect(page.locator('#progHash')).toContainText(/Program hash:\s*\d+/);
  });

  test('1b. Seed evaluation - invalid word count shows error', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });

    await page.fill('#seedInput', 'abandon abandon');
    await page.click('#tryBtn');

    await expect(page.locator('#tryStatus')).toContainText('Need exactly 12 words');
    await expect(page.locator('#claimCard')).toBeHidden();
  });

  test('1c. Seed evaluation - unknown word shows error', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });

    await page.fill('#seedInput', 'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon xyznotaword');
    await page.click('#tryBtn');

    await expect(page.locator('#tryStatus')).toContainText('Unknown word');
    await expect(page.locator('#claimCard')).toBeHidden();
  });

  test('2. Seed evaluation - valid seed', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });
    
    // Enter a valid seed (any seed works with identity matrices)
    const testSeed = 'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about';
    await page.fill('#seedInput', testSeed);
    
    // Click evaluate
    await page.click('#tryBtn');
    
    // Should show valid result
    await expect(page.locator('#tryStatus')).toContainText('VALID SEED FOUND', { timeout: 10000 });
    await expect(page.locator('#tryStatus')).toHaveClass(/success/);
    
    // Claim card should appear
    await expect(page.locator('#claimCard')).toBeVisible();
  });

  test('3. Seed evaluation - random seed also valid (identity matrices)', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });
    
    // Click random to generate a seed
    await page.click('button:text("Random")');
    
    // Verify input has 12 words
    const seedValue = await page.inputValue('#seedInput');
    const words = seedValue.trim().split(/\s+/);
    expect(words.length).toBe(12);
    
    // Evaluate it
    await page.click('#tryBtn');
    
    // Should also be valid (all identity matrices)
    await expect(page.locator('#tryStatus')).toContainText('VALID SEED FOUND', { timeout: 10000 });
  });

  test('4. Noir prover initialization', async ({ page }) => {
    await page.goto('/');
    
    // Wait for full initialization including Noir
    await expect(page.locator('#log')).toContainText('Noir prover ready', { timeout: 60000 });
  });

  test('5. Full proof generation flow', async ({ page }) => {
    test.setTimeout(180000); // 3 min for proof generation
    
    await page.goto('/');
    
    // Wait for everything to initialize
    await expect(page.locator('#log')).toContainText('Noir prover ready', { timeout: 60000 });
    
    // Enter seed and evaluate
    await page.fill('#seedInput', 'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about');
    await page.click('#tryBtn');
    await expect(page.locator('#claimCard')).toBeVisible({ timeout: 10000 });
    
    // Click generate proof
    await page.click('#claimBtn');
    
    // Wait for witness generation
    await expect(page.locator('#log')).toContainText('Noir witness generated', { timeout: 30000 });
    
    // Wait for proof generation (this takes a while)
    await expect(page.locator('#log')).toContainText('Proof generated', { timeout: 120000 });
    
    // Wait for local verification
    await expect(page.locator('#log')).toContainText('Proof verified locally', { timeout: 30000 });
    
    // Should show success status
    await expect(page.locator('#claimStatus')).toContainText('Proof ready', { timeout: 10000 });
  });

  test('6. Batch brute force UI', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });
    
    // Set small batch size
    await page.fill('#batchSize', '100');
    await page.fill('#startIndex', '0');
    
    // Start batch
    await page.click('#batchBtn');
    
    // Should see progress
    await expect(page.locator('#log')).toContainText('Starting batch', { timeout: 5000 });
    
    // With identity matrices, should find valid immediately
    await expect(page.locator('#log')).toContainText('FOUND', { timeout: 10000 });
    
    // Stop batch
    await page.click('button:text("Stop")');
  });

  test('7. Code viewer toggle', async ({ page }) => {
    await page.goto('/');
    await expect(page.locator('#log')).toContainText('WASM ready', { timeout: 30000 });
    
    // Code card should be hidden initially
    await expect(page.locator('#codeCard')).toBeHidden();
    
    // Click to show
    await page.click('button:text("View Obfuscated Program")');
    await expect(page.locator('#codeCard')).toBeVisible();
    
    // Check tabs work
    await page.click('.tab:text("Rust Struct")');
    await expect(page.locator('#codeContent')).toContainText('ObfuscatedProgram');
    
    await page.click('.tab:text("Matrices")');
    await expect(page.locator('#codeContent')).toContainText('M[0]');
  });

});

test.describe('Contract Integration', () => {
  
  test('Contract state verification via RPC', async ({ request }) => {
    // Check honeypot is active via RPC call
    const claimedCall = await request.post(RPC_URL, {
      data: {
        jsonrpc: '2.0',
        id: 1,
        method: 'eth_call',
        params: [{
          to: HONEYPOT_ADDRESS,
          data: '0xe834a834' // claimed() selector
        }, 'latest']
      }
    });
    
    const claimedResult = await claimedCall.json();
    // Should return false (0x0...0)
    expect(claimedResult.result).toBe('0x0000000000000000000000000000000000000000000000000000000000000000');
    
    // Check prize amount
    const prizeCall = await request.post(RPC_URL, {
      data: {
        jsonrpc: '2.0',
        id: 2,
        method: 'eth_call',
        params: [{
          to: HONEYPOT_ADDRESS,
          data: '0xe3ac5d26' // prize() selector
        }, 'latest']
      }
    });
    
    const prizeResult = await prizeCall.json();
    // Should be 0.1 ETH = 1e17 wei
    expect(BigInt(prizeResult.result)).toBe(BigInt('100000000000000000'));
  });

});
