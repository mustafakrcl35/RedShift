use ark_bls12_381::Fr as Fp;
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain};
use redshift::relative_hamming_distance; 

#[test]
fn test_hamming_distance_zero() {
    let coeffs = vec![Fp::from(1u64), Fp::from(2u64)];
    let f = DensePolynomial::from_coefficients_vec(coeffs.clone());
    let g = DensePolynomial::from_coefficients_vec(coeffs);

    let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
    let elements: Vec<Fp> = domain.elements().collect();

    let distance = relative_hamming_distance(&f, &g, &elements);
    assert_eq!(distance, 0.0);
}

#[test]
fn test_hamming_distance_nonzero() {
    let f = DensePolynomial::from_coefficients_vec(vec![Fp::from(1u64), Fp::from(2u64)]);
    let g = DensePolynomial::from_coefficients_vec(vec![Fp::from(1u64), Fp::from(3u64)]);

    let domain = Radix2EvaluationDomain::<Fp>::new(4).unwrap();
    let elements: Vec<Fp> = domain.elements().collect();

    let distance = relative_hamming_distance(&f, &g, &elements);
    assert!(distance > 0.0 && distance < 1.0);
}
