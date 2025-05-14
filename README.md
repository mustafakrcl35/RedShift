# RedShift

**RedShift** is a Rust implementation of the [RedShift protocol](https://eprint.iacr.org/2019/1400) for zero-knowledge proofs over polynomial commitments.

## Features

- Polynomial commitment scheme based on the `arkworks` ecosystem.
- Efficient FFT-based polynomial operations.
- Modular design for prover and verifier separation.
- Generic over finite fields supporting different curve parameters.
- Simple example included for demonstration and testing.

## Getting Started

### Requirements

- Rust (>= 1.74)
- Cargo package manager

### Build

git clone https://github.com/mustafakrcl35/RedShift.git
cd RedShift
cargo build --release
