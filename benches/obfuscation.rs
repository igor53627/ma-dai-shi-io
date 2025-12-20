//! Benchmarks for LiO obfuscation performance
//!
//! Run with: `cargo bench --bench obfuscation`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ma_dai_shi_io::circuit::Circuit;
use ma_dai_shi_io::lio::{LiO, LiOParams};

fn bench_obfuscate(c: &mut Criterion) {
    let mut group = c.benchmark_group("obfuscation");

    for num_gates in [5, 10, 25, 50] {
        let num_wires = (num_gates + 2).min(64);
        let circuit = Circuit::random_r57(num_wires, num_gates);

        group.throughput(Throughput::Elements(num_gates as u64));
        group.bench_with_input(
            BenchmarkId::new("gates", num_gates),
            &circuit,
            |b, circuit| {
                b.iter(|| {
                    let lio = LiO::new(LiOParams::default());
                    lio.obfuscate(circuit).unwrap()
                })
            },
        );
    }

    group.finish();
}

fn bench_obfuscate_varying_wires(c: &mut Criterion) {
    let mut group = c.benchmark_group("obfuscation_wires");

    let num_gates = 10;
    for num_wires in [8, 16, 32, 64] {
        let circuit = Circuit::random_r57(num_wires, num_gates);

        group.bench_with_input(
            BenchmarkId::new("wires", num_wires),
            &circuit,
            |b, circuit| {
                b.iter(|| {
                    let lio = LiO::new(LiOParams::default());
                    lio.obfuscate(circuit).unwrap()
                })
            },
        );
    }

    group.finish();
}

fn bench_obfuscated_size(c: &mut Criterion) {
    let mut group = c.benchmark_group("obfuscated_size");

    for num_gates in [5, 10, 25] {
        let num_wires = num_gates + 2;
        let circuit = Circuit::random_r57(num_wires, num_gates);
        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        group.bench_with_input(
            BenchmarkId::new("size_bytes", num_gates),
            &obf,
            |b, obf| b.iter(|| obf.size_bytes()),
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_obfuscate,
    bench_obfuscate_varying_wires,
    bench_obfuscated_size
);
criterion_main!(benches);
