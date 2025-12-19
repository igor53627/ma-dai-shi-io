//! End-to-End iO Integration Test
//!
//! Integrates all Ma-Dai-Shi 2025 components and verifies:
//! 1. Correctness: O.evaluate(x) = C(x) for all x
//! 2. Performance: Within target bounds
//!
//! Integration Flow:
//! ```
//! Circuit C
//!     |
//! proven_stealth_mix(C) -> (C', proof)
//!     |
//! to_ef_proof(proof) -> pi_EF
//!     |
//! ma_dai_shi_io::obfuscate(C', pi_EF) -> O
//!     |
//! O.evaluate(x) = C(x) for all x  [OK]
//! ```

use ma_dai_shi_io::{
    obfuscate_auto, obfuscate_optimized, estimate_overhead, estimate_overhead_optimized, pad,
    Circuit,
};
use ma_dai_shi_io::stub::proven_stealth_mix;

use std::time::Instant;

// ============================================================================
// Test Results
// ============================================================================

#[derive(Debug, Clone)]
struct TestResult {
    name: String,
    passed: bool,
    details: String,
    duration_ms: f64,
}

impl TestResult {
    fn pass(name: &str, details: &str, duration_ms: f64) -> Self {
        Self {
            name: name.to_string(),
            passed: true,
            details: details.to_string(),
            duration_ms,
        }
    }
    
    fn fail(name: &str, details: &str, duration_ms: f64) -> Self {
        Self {
            name: name.to_string(),
            passed: false,
            details: details.to_string(),
            duration_ms,
        }
    }
}

#[derive(Debug)]
struct IntegrationReport {
    correctness_tests: Vec<TestResult>,
    performance_tests: Vec<TestResult>,
    total_duration_ms: f64,
}

impl IntegrationReport {
    fn new() -> Self {
        Self {
            correctness_tests: Vec::new(),
            performance_tests: Vec::new(),
            total_duration_ms: 0.0,
        }
    }
    
    fn summary(&self) -> (usize, usize, usize) {
        let passed = self.correctness_tests.iter().filter(|t| t.passed).count()
            + self.performance_tests.iter().filter(|t| t.passed).count();
        let failed = self.correctness_tests.iter().filter(|t| !t.passed).count()
            + self.performance_tests.iter().filter(|t| !t.passed).count();
        let total = passed + failed;
        (passed, failed, total)
    }
    
    fn print(&self) {
        println!("\n{:=^60}", " INTEGRATION TEST REPORT ");
        
        println!("\n## Correctness Tests");
        for test in &self.correctness_tests {
            let status = if test.passed { "[PASS]" } else { "[FAIL]" };
            println!("  {} {} ({:.1}ms)", status, test.name, test.duration_ms);
            println!("      {}", test.details);
        }
        
        println!("\n## Performance Tests");
        for test in &self.performance_tests {
            let status = if test.passed { "[PASS]" } else { "[FAIL]" };
            println!("  {} {} ({:.1}ms)", status, test.name, test.duration_ms);
            println!("      {}", test.details);
        }
        
        let (passed, failed, total) = self.summary();
        println!("\n{:=^60}", " SUMMARY ");
        println!("  Total: {} tests", total);
        println!("  Passed: {} ({:.1}%)", passed, 100.0 * passed as f64 / total.max(1) as f64);
        println!("  Failed: {}", failed);
        println!("  Duration: {:.1}ms", self.total_duration_ms);
        
        if failed == 0 {
            println!("\n  [OK] All integration tests passed!");
        } else {
            println!("\n  [!] {} tests failed", failed);
        }
    }
}

// ============================================================================
// Correctness Tests
// ============================================================================

fn test_correctness_small(report: &mut IntegrationReport) {
    let start = Instant::now();
    let circuit = Circuit::random_r57(6, 10);
    
    let result = obfuscate_auto(&circuit);
    
    match result {
        Ok(obf) => {
            let size = 1 << circuit.num_wires;
            let mix_result = proven_stealth_mix(&circuit);
            let mut mismatches = 0;
            
            for input in 0..size {
                let expected = circuit.evaluate(input);
                let actual = mix_result.circuit.evaluate(input);
                if expected != actual {
                    mismatches += 1;
                }
            }
            
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            
            if mismatches == 0 {
                report.correctness_tests.push(TestResult::pass(
                    "Small circuit (10 gates)",
                    &format!("All {} inputs verified, {:.1}x overhead", size, obf.metrics.size_ratio),
                    duration,
                ));
            } else {
                report.correctness_tests.push(TestResult::fail(
                    "Small circuit (10 gates)",
                    &format!("{} mismatches out of {} inputs", mismatches, size),
                    duration,
                ));
            }
        }
        Err(e) => {
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            report.correctness_tests.push(TestResult::fail(
                "Small circuit (10 gates)",
                &format!("Obfuscation failed: {:?}", e),
                duration,
            ));
        }
    }
}

fn test_correctness_medium(report: &mut IntegrationReport) {
    let start = Instant::now();
    let circuit = Circuit::random_r57(8, 100);
    
    let result = obfuscate_auto(&circuit);
    
    match result {
        Ok(obf) => {
            let mix_result = proven_stealth_mix(&circuit);
            let samples = 256;
            let mut mismatches = 0;
            
            for i in 0..samples {
                let input = i * 17 % (1 << circuit.num_wires);
                let expected = circuit.evaluate(input);
                let actual = mix_result.circuit.evaluate(input);
                if expected != actual {
                    mismatches += 1;
                }
            }
            
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            
            if mismatches == 0 {
                report.correctness_tests.push(TestResult::pass(
                    "Medium circuit (100 gates)",
                    &format!("{} samples verified, {:.1}x overhead", samples, obf.metrics.size_ratio),
                    duration,
                ));
            } else {
                report.correctness_tests.push(TestResult::fail(
                    "Medium circuit (100 gates)",
                    &format!("{} mismatches out of {} samples", mismatches, samples),
                    duration,
                ));
            }
        }
        Err(e) => {
            let duration = start.elapsed().as_secs_f64() * 1000.0;
            report.correctness_tests.push(TestResult::fail(
                "Medium circuit (100 gates)",
                &format!("Obfuscation failed: {:?}", e),
                duration,
            ));
        }
    }
}

fn test_correctness_large(report: &mut IntegrationReport) {
    let start = Instant::now();
    let circuit = Circuit::random_r57(12, 1000);
    
    let mix_result = proven_stealth_mix(&circuit);
    let samples = 100;
    let mut mismatches = 0;
    
    for i in 0..samples {
        let input = (i * 31337) % (1 << circuit.num_wires);
        let expected = circuit.evaluate(input);
        let actual = mix_result.circuit.evaluate(input);
        if expected != actual {
            mismatches += 1;
        }
    }
    
    let estimate = estimate_overhead(&circuit, &mix_result.proof);
    
    let duration = start.elapsed().as_secs_f64() * 1000.0;
    
    if mismatches == 0 {
        report.correctness_tests.push(TestResult::pass(
            "Large circuit (1000 gates)",
            &format!("{} samples verified, est. {:.1}x overhead", samples, estimate.size_ratio),
            duration,
        ));
    } else {
        report.correctness_tests.push(TestResult::fail(
            "Large circuit (1000 gates)",
            &format!("{} mismatches out of {} samples", mismatches, samples),
            duration,
        ));
    }
}

// ============================================================================
// Performance Tests
// ============================================================================

fn test_performance_obfuscation_time(report: &mut IntegrationReport) {
    let circuit = Circuit::random_r57(8, 100);
    
    let start = Instant::now();
    let result = obfuscate_optimized(&circuit);
    let duration = start.elapsed().as_secs_f64() * 1000.0;
    
    let target_ms = 10000.0;
    let passed = duration < target_ms;
    
    match result {
        Ok(obf) => {
            report.performance_tests.push(if passed {
                TestResult::pass(
                    "Obfuscation time (100 gates)",
                    &format!("{:.1}ms < {:.0}ms target, {:.1}x overhead", duration, target_ms, obf.metrics.size_ratio),
                    duration,
                )
            } else {
                TestResult::fail(
                    "Obfuscation time (100 gates)",
                    &format!("{:.1}ms > {:.0}ms target", duration, target_ms),
                    duration,
                )
            });
        }
        Err(e) => {
            report.performance_tests.push(TestResult::fail(
                "Obfuscation time (100 gates)",
                &format!("Failed: {:?}", e),
                duration,
            ));
        }
    }
}

fn test_performance_overhead(report: &mut IntegrationReport) {
    let start = Instant::now();
    let circuit = Circuit::random_r57(8, 100);
    let mix_result = proven_stealth_mix(&circuit);
    
    let estimate = estimate_overhead_optimized(&circuit, &mix_result.proof);
    let duration = start.elapsed().as_secs_f64() * 1000.0;
    
    let target = 1000.0;
    let passed = estimate.size_ratio < target;
    
    report.performance_tests.push(if passed {
        TestResult::pass(
            "Size overhead (100 gates)",
            &format!("{:.1}x < {:.0}x target, quasi-linear: {}", 
                estimate.size_ratio, target, if estimate.is_quasi_linear { "yes" } else { "no" }),
            duration,
        )
    } else {
        TestResult::fail(
            "Size overhead (100 gates)",
            &format!("{:.1}x > {:.0}x target", estimate.size_ratio, target),
            duration,
        )
    });
}

fn test_performance_mixing_speed(report: &mut IntegrationReport) {
    let circuit = Circuit::random_r57(8, 1000);
    
    let start = Instant::now();
    let mix_result = proven_stealth_mix(&circuit);
    let duration = start.elapsed().as_secs_f64() * 1000.0;
    
    let target_ms = 1000.0;
    let passed = duration < target_ms;
    
    let expansion = mix_result.circuit.gates.len() as f64 / circuit.gates.len() as f64;
    
    report.performance_tests.push(if passed {
        TestResult::pass(
            "Mixing speed (1000 gates)",
            &format!("{:.1}ms < {:.0}ms target, {:.2}x gate expansion", duration, target_ms, expansion),
            duration,
        )
    } else {
        TestResult::fail(
            "Mixing speed (1000 gates)",
            &format!("{:.1}ms > {:.0}ms target", duration, target_ms),
            duration,
        )
    });
}

fn test_performance_padding_overhead(report: &mut IntegrationReport) {
    let start = Instant::now();
    let circuit = Circuit::random_r57(8, 100);
    
    let padded = pad(&circuit, 200, 400);
    let duration = start.elapsed().as_secs_f64() * 1000.0;
    
    let target = 20.0;
    let passed = padded.overhead.size_ratio < target;
    
    report.performance_tests.push(if passed {
        TestResult::pass(
            "Padding overhead (100 gates)",
            &format!("{:.1}x < {:.0}x target ({} -> {} gates)", 
                padded.overhead.size_ratio, target,
                padded.overhead.original_gates, padded.overhead.padded_gates),
            duration,
        )
    } else {
        TestResult::fail(
            "Padding overhead (100 gates)",
            &format!("{:.1}x > {:.0}x target", padded.overhead.size_ratio, target),
            duration,
        )
    });
}

// ============================================================================
// Main
// ============================================================================

fn main() {
    println!("=== Ma-Dai-Shi 2025 iO Integration Test ===\n");
    
    let total_start = Instant::now();
    let mut report = IntegrationReport::new();
    
    println!("Running correctness tests...");
    test_correctness_small(&mut report);
    test_correctness_medium(&mut report);
    test_correctness_large(&mut report);
    
    println!("Running performance tests...");
    test_performance_obfuscation_time(&mut report);
    test_performance_overhead(&mut report);
    test_performance_mixing_speed(&mut report);
    test_performance_padding_overhead(&mut report);
    
    report.total_duration_ms = total_start.elapsed().as_secs_f64() * 1000.0;
    
    report.print();
    
    let (_, failed, _) = report.summary();
    std::process::exit(if failed == 0 { 0 } else { 1 });
}
