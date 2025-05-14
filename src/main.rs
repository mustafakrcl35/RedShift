use ark_bls12_381::Fr as Fp;
use ark_ff::{Field, UniformRand};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Polynomial, Radix2EvaluationDomain,
    DenseUVPolynomial,  // <-- Add this import
};
use ark_std::rand::Rng;
use ark_std::test_rng;

fn relative_hamming_distance<F: Field>(
    f: &DensePolynomial<F>,
    g: &DensePolynomial<F>,
    domain: &[F],
) -> f64 {
    let mut mismatch_count = 0;

    for &x in domain.iter() {
        if f.evaluate(&x) != g.evaluate(&x) {
            mismatch_count += 1;
        }
    }

    mismatch_count as f64 / domain.len() as f64
}


fn main() {
    let rng = &mut test_rng();

    // Define two random polynomials of degree at most 4
    let f_coeffs: Vec<Fp> = (0..5).map(|_| Fp::rand(rng)).collect();
    let g_coeffs: Vec<Fp> = (0..5).map(|_| Fp::rand(rng)).collect();

    let f = DensePolynomial::from_coefficients_vec(f_coeffs);
    let g = DensePolynomial::from_coefficients_vec(g_coeffs);

    // Create an FFT-friendly Radix2EvaluationDomain of size 8 (must be a power of two)
    let domain = Radix2EvaluationDomain::<Fp>::new(8).unwrap();

    // Collect all domain elements (roots of unity)
    let domain_elements: Vec<Fp> = domain.elements().collect();

    // Compute the relative Hamming distance
    let distance = relative_hamming_distance(&f, &g, &domain_elements);

    println!("Relative Hamming Distance: {}", distance);
}