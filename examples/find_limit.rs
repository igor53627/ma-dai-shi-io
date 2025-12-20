//! Find the practical limits of truth-table iO
//!
//! Run with: cargo run --release --example find_limit

use ma_dai_shi_io::crypto::{BytecodeProgram, GeneralizedCanonicalSmallObf, SmallObf};
use std::time::Instant;

fn main() {
    println!("Benchmarking GeneralizedCanonicalSmallObf...\n");
    println!(
        "{:>6} {:>14} {:>12} {:>12}",
        "Bits", "Rows", "Table Size", "Obf Time"
    );
    println!("{:-<6} {:->14} {:->12} {:->12}", "", "", "", "");

    for n_bytes in [1, 2, 3, 4] {
        let n_bits = n_bytes * 8;
        let n_rows: u64 = 1u64 << n_bits;

        let size_str = if n_rows < 1024 {
            format!("{} B", n_rows)
        } else if n_rows < 1024 * 1024 {
            format!("{} KB", n_rows / 1024)
        } else {
            format!("{} MB", n_rows / (1024 * 1024))
        };

        let obf = GeneralizedCanonicalSmallObf::new(n_bits);
        let prog = BytecodeProgram::xor_all(n_bytes);

        let start = Instant::now();
        let obfuscated = obf.obfuscate(&prog);
        let elapsed = start.elapsed();

        println!(
            "{:>6} {:>14} {:>12} {:>12.2?}",
            n_bits, n_rows, size_str, elapsed
        );

        // Verify correctness
        let test_input: Vec<u8> = (0..n_bytes).map(|i| (i * 0x55) as u8).collect();
        let output = obf.eval(&obfuscated, &test_input);
        let expected: u8 = test_input.iter().fold(0, |acc, &b| acc ^ b);
        assert_eq!(output[0], expected, "Correctness check failed!");
    }

    println!("\n[OK] All correctness checks passed");

    println!("\n=== Practical Limits ===");
    println!("| Bits | Table Size | Time      | Recommendation |");
    println!("|------|------------|-----------|----------------|");
    println!("| 8    | 256 B      | <1ms      | Instant        |");
    println!("| 16   | 64 KB      | <1ms      | Default        |");
    println!("| 24   | 16 MB      | ~10ms     | Practical max  |");
    println!("| 30   | 1 GB       | ~500ms    | Hard limit     |");
    println!("| 32   | 4 GB       | ~2s       | Memory limit   |");
    println!("| 64   | 18 EB      | N/A       | Infeasible     |");
}
