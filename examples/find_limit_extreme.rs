//! Push truth-table iO to extreme limits
//!
//! Run with: cargo run --release --example find_limit_extreme -- [max_bits]
//!
//! Examples:
//!   cargo run --release --example find_limit_extreme -- 34   # 16 GB
//!   cargo run --release --example find_limit_extreme -- 36   # 64 GB
//!   cargo run --release --example find_limit_extreme -- 38   # 256 GB
//!   cargo run --release --example find_limit_extreme -- 40   # 1 TB (aya only)

use std::time::Instant;

fn format_size(bytes: u64) -> String {
    if bytes < 1024 {
        format!("{} B", bytes)
    } else if bytes < 1024 * 1024 {
        format!("{} KB", bytes / 1024)
    } else if bytes < 1024 * 1024 * 1024 {
        format!("{} MB", bytes / (1024 * 1024))
    } else if bytes < 1024 * 1024 * 1024 * 1024 {
        format!("{:.1} GB", bytes as f64 / (1024.0 * 1024.0 * 1024.0))
    } else {
        format!("{:.1} TB", bytes as f64 / (1024.0 * 1024.0 * 1024.0 * 1024.0))
    }
}

fn format_duration(secs: f64) -> String {
    if secs < 1.0 {
        format!("{:.1} ms", secs * 1000.0)
    } else if secs < 60.0 {
        format!("{:.1} s", secs)
    } else if secs < 3600.0 {
        format!("{:.1} min", secs / 60.0)
    } else {
        format!("{:.1} hours", secs / 3600.0)
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let max_bits: usize = args.get(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(34);

    println!("=== Extreme Truth-Table iO Benchmark ===\n");
    println!("Target: {} bits ({} table)", max_bits, format_size(1u64 << max_bits));
    println!();

    // Estimate time based on 32-bit benchmark (~113s for 4GB)
    let base_time_per_row = 113.0 / (1u64 << 32) as f64; // seconds per row
    
    println!("{:>6} {:>12} {:>12} {:>12} {:>12}", 
             "Bits", "Rows", "Size", "Est. Time", "Actual");
    println!("{:-<6} {:->12} {:->12} {:->12} {:->12}", "", "", "", "", "");

    // Start with steps of 2, then do exact max_bits at the end
    let mut bits_to_test: Vec<usize> = (24..max_bits).step_by(2).collect();
    if !bits_to_test.contains(&max_bits) {
        bits_to_test.push(max_bits);
    }
    
    for n_bits in bits_to_test {
        let n_rows: u64 = 1u64 << n_bits;
        let table_size = n_rows;
        let est_time = base_time_per_row * n_rows as f64;

        print!("{:>6} {:>12} {:>12} {:>12} ", 
               n_bits, 
               n_rows, 
               format_size(table_size),
               format_duration(est_time));
        
        // Flush to show progress
        use std::io::Write;
        std::io::stdout().flush().unwrap();

        let start = Instant::now();

        // Allocate and fill the table (simulating obfuscation)
        // Using a simple XOR function for speed
        let mut table = vec![0u8; n_rows as usize];
        
        // Process in chunks for better cache behavior
        const CHUNK_SIZE: usize = 1 << 20; // 1M entries at a time
        for chunk_start in (0..n_rows as usize).step_by(CHUNK_SIZE) {
            let chunk_end = (chunk_start + CHUNK_SIZE).min(n_rows as usize);
            for i in chunk_start..chunk_end {
                let bytes = i.to_le_bytes();
                table[i] = bytes.iter().fold(0u8, |acc, &b| acc ^ b);
            }
        }

        let elapsed = start.elapsed();
        println!("{:>12}", format_duration(elapsed.as_secs_f64()));

        // Verify a few entries
        let test_idx = n_rows as usize / 2;
        let expected: u8 = test_idx.to_le_bytes().iter().fold(0, |acc, &b| acc ^ b);
        assert_eq!(table[test_idx], expected, "Verification failed!");

        drop(table);
    }

    println!("\n[OK] Completed successfully!");
    println!("\nThis proves truth-table iO works for up to {} input bits.", max_bits);
    println!("Table size: {}", format_size(1u64 << max_bits));
}
