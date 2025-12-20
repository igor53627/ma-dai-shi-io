//! Benchmarks for LiO evaluation performance
//!
//! Run with: `cargo bench --bench evaluation`

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use ma_dai_shi_io::circuit::Circuit;
use ma_dai_shi_io::lio::{LiO, LiOParams};

fn bench_evaluate(c: &mut Criterion) {
    let mut group = c.benchmark_group("evaluation");

    for num_gates in [5, 10, 25, 50] {
        let num_wires = (num_gates + 2).min(64);
        let circuit = Circuit::random_r57(num_wires, num_gates);
        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        group.throughput(Throughput::Elements(num_gates as u64));
        group.bench_with_input(BenchmarkId::new("gates", num_gates), &obf, |b, obf| {
            let mut input = 0usize;
            b.iter(|| {
                input = (input + 1) % (1 << num_wires.min(16));
                obf.evaluate(input).unwrap()
            })
        });
    }

    group.finish();
}

fn bench_evaluate_with_seh_check(c: &mut Criterion) {
    let mut group = c.benchmark_group("evaluation_seh");

    for num_gates in [5, 10, 25] {
        let num_wires = num_gates + 2;
        let circuit = Circuit::random_r57(num_wires, num_gates);
        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        group.bench_with_input(
            BenchmarkId::new("gates_with_seh", num_gates),
            &obf,
            |b, obf| {
                let mut input = 0usize;
                b.iter(|| {
                    input = (input + 1) % (1 << num_wires.min(16));
                    obf.evaluate_with_seh_check(input).unwrap()
                })
            },
        );
    }

    group.finish();
}

fn bench_verify_seh(c: &mut Criterion) {
    let mut group = c.benchmark_group("seh_verification");

    for num_gates in [5, 10, 25] {
        let num_wires = num_gates + 2;
        let circuit = Circuit::random_r57(num_wires, num_gates);
        let lio = LiO::new(LiOParams::default());
        let obf = lio.obfuscate(&circuit).unwrap();

        group.bench_with_input(
            BenchmarkId::new("wires", num_wires),
            &obf,
            |b, obf| b.iter(|| obf.verify_seh()),
        );
    }

    group.finish();
}

fn bench_correctness(c: &mut Criterion) {
    let mut group = c.benchmark_group("correctness_check");

    let num_gates = 10;
    let num_wires = 8;
    let circuit = Circuit::random_r57(num_wires, num_gates);
    let lio = LiO::new(LiOParams::default());
    let obf = lio.obfuscate(&circuit).unwrap();

    group.bench_function("obf_vs_plaintext", |b| {
        let mut input = 0usize;
        b.iter(|| {
            input = (input + 1) % (1 << num_wires);
            let obf_result = obf.evaluate(input).unwrap();
            let plain_result = circuit.evaluate(input);
            assert_eq!(obf_result, plain_result);
            obf_result
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_evaluate,
    bench_evaluate_with_seh_check,
    bench_verify_seh,
    bench_correctness
);
criterion_main!(benches);
