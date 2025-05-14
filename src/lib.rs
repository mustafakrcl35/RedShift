use ark_poly::univariate::DensePolynomial;
use ark_ff::Field;
use ark_poly::Polynomial;


/// Computes the relative Hamming distance between two polynomials over a given domain.
pub fn relative_hamming_distance<F: Field>(
    f: &DensePolynomial<F>,
    g: &DensePolynomial<F>,
    domain: &[F],
) -> f64 {
    let mismatches = domain.iter().filter(|&&x| f.evaluate(&x) != g.evaluate(&x)).count();
    mismatches as f64 / domain.len() as f64
}
