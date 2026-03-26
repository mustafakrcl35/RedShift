//! PLONK-style arithmetic constraint system.
//!
//! Each gate enforces: q_L·a + q_R·b + q_M·a·b + q_O·c + q_C = 0
//! Copy constraints are handled via a grand-product permutation argument.

use ark_ff::PrimeField;
use crate::polynomial::vanishing_poly;

// ── Gate & Circuit ─────────────────────────────────────────────────────────────

/// Single arithmetic gate with PLONK selectors.
pub struct Gate<F: PrimeField> {
    pub q_l: F,
    pub q_r: F,
    pub q_m: F,
    pub q_o: F,
    pub q_c: F,
}

/// Full circuit: n gates with their wire witness values.
pub struct Circuit<F: PrimeField> {
    pub gates: Vec<Gate<F>>,
    pub a: Vec<F>,
    pub b: Vec<F>,
    pub c: Vec<F>,
}

impl<F: PrimeField> Circuit<F> {
    /// Return true iff every gate constraint is satisfied.
    pub fn is_satisfied(&self) -> bool {
        self.gates.iter().enumerate().all(|(i, g)| {
            g.q_l * self.a[i]
                + g.q_r * self.b[i]
                + g.q_m * self.a[i] * self.b[i]
                + g.q_o * self.c[i]
                + g.q_c
                == F::zero()
        })
    }

    /// Lagrange-interpolate a(x), b(x), c(x) over `domain`.
    pub fn wire_polynomials(&self, domain: &[F]) -> (Vec<F>, Vec<F>, Vec<F>) {
        (
            lagrange_interpolate(domain, &self.a),
            lagrange_interpolate(domain, &self.b),
            lagrange_interpolate(domain, &self.c),
        )
    }

    /// Build the combined gate constraint polynomial:
    /// f_gate(x) = q_L(x)·a(x) + q_R(x)·b(x) + q_M(x)·a(x)·b(x) + q_O(x)·c(x) + q_C(x)
    ///
    /// This polynomial must vanish on `domain` iff the circuit is satisfied.
    pub fn gate_constraint_poly(&self, domain: &[F]) -> Vec<F> {
        let (a_p, b_p, c_p) = self.wire_polynomials(domain);

        let q_l_vals: Vec<F> = self.gates.iter().map(|g| g.q_l).collect();
        let q_r_vals: Vec<F> = self.gates.iter().map(|g| g.q_r).collect();
        let q_m_vals: Vec<F> = self.gates.iter().map(|g| g.q_m).collect();
        let q_o_vals: Vec<F> = self.gates.iter().map(|g| g.q_o).collect();
        let q_c_vals: Vec<F> = self.gates.iter().map(|g| g.q_c).collect();

        let q_l = lagrange_interpolate(domain, &q_l_vals);
        let q_r = lagrange_interpolate(domain, &q_r_vals);
        let q_m = lagrange_interpolate(domain, &q_m_vals);
        let q_o = lagrange_interpolate(domain, &q_o_vals);
        let q_c = lagrange_interpolate(domain, &q_c_vals);

        let mut f = poly_mul(&q_l, &a_p);
        f = poly_add(&f, &poly_mul(&q_r, &b_p));
        f = poly_add(&f, &poly_mul(&q_m, &poly_mul(&a_p, &b_p)));
        f = poly_add(&f, &poly_mul(&q_o, &c_p));
        f = poly_add(&f, &q_c);
        f
    }

    /// Compute the quotient t(x) = f_gate(x) / Z_H(x).
    ///
    /// Returns `None` if the division is not exact (circuit unsatisfied).
    pub fn quotient_poly(&self, domain: &[F]) -> Option<Vec<F>> {
        let f_gate = self.gate_constraint_poly(domain);
        let z_h = vanishing_poly(domain);
        let (quot, rem) = poly_div_rem(&f_gate, &z_h);
        if rem.iter().all(|c| c.is_zero()) {
            Some(quot)
        } else {
            None
        }
    }
}

// ── Permutation argument ───────────────────────────────────────────────────────

/// Copy-constraint permutation for a, b, c wires.
///
/// `sigma_x[i]` is the coset-encoded index that wire x[i] maps to in the full
/// 3n-wire vector: a-wires occupy 0..n, b-wires n..2n, c-wires 2n..3n.
pub struct PermutationArgument<F: PrimeField> {
    pub sigma_a: Vec<usize>,
    pub sigma_b: Vec<usize>,
    pub sigma_c: Vec<usize>,
    _phantom: std::marker::PhantomData<F>,
}

impl<F: PrimeField> PermutationArgument<F> {
    pub fn new(sigma_a: Vec<usize>, sigma_b: Vec<usize>, sigma_c: Vec<usize>) -> Self {
        Self { sigma_a, sigma_b, sigma_c, _phantom: std::marker::PhantomData }
    }

    /// Compute grand-product evaluations Z(ω^0), …, Z(ω^n).
    ///
    /// Z(ω^0) = 1; each step multiplies by the ratio of numerator / denominator
    /// accumulators.  For a valid permutation, Z(ω^n) = 1.
    pub fn grand_product(&self, circuit: &Circuit<F>, beta: F, gamma: F) -> Vec<F> {
        let n = circuit.gates.len();
        let mut z: Vec<F> = Vec::with_capacity(n + 1);
        z.push(F::one());

        for i in 0..n {
            let id_a = F::from(i as u64);
            let id_b = F::from((n + i) as u64);
            let id_c = F::from((2 * n + i) as u64);

            let sa = F::from(self.sigma_a[i] as u64);
            let sb = F::from(self.sigma_b[i] as u64);
            let sc = F::from(self.sigma_c[i] as u64);

            let num = (circuit.a[i] + beta * id_a + gamma)
                * (circuit.b[i] + beta * id_b + gamma)
                * (circuit.c[i] + beta * id_c + gamma);

            let den = (circuit.a[i] + beta * sa + gamma)
                * (circuit.b[i] + beta * sb + gamma)
                * (circuit.c[i] + beta * sc + gamma);

            let prev = *z.last().unwrap();
            z.push(prev * num * den.inverse().expect("denominator must be nonzero"));
        }

        z
    }

    /// Check Z(ω^0) = 1 and Z(ω^n) = 1 (wrap-around condition).
    pub fn check_grand_product(&self, z_evals: &[F]) -> bool {
        z_evals.first() == Some(&F::one()) && z_evals.last() == Some(&F::one())
    }
}

// ── Polynomial helpers ─────────────────────────────────────────────────────────

/// Lagrange interpolation: find the unique polynomial of degree < n
/// that passes through all (domain[i], values[i]) pairs.
pub fn lagrange_interpolate<F: PrimeField>(domain: &[F], values: &[F]) -> Vec<F> {
    assert_eq!(domain.len(), values.len(), "domain/values length mismatch");
    let n = domain.len();
    if n == 0 {
        return vec![];
    }
    if n == 1 {
        return vec![values[0]];
    }

    let mut result = vec![F::zero(); n];

    for i in 0..n {
        if values[i].is_zero() {
            continue;
        }
        // Numerator: ∏_{j≠i} (x − domain[j])
        let mut num = vec![F::one()];
        for j in 0..n {
            if j == i {
                continue;
            }
            num = poly_mul(&num, &[-domain[j], F::one()]);
        }
        // Denominator: ∏_{j≠i} (domain[i] − domain[j])
        let mut den = F::one();
        for j in 0..n {
            if j == i {
                continue;
            }
            den *= domain[i] - domain[j];
        }
        let scale = values[i] * den.inverse().expect("domain points must be distinct");
        let term: Vec<F> = num.iter().map(|&c| c * scale).collect();
        result = poly_add(&result, &term);
    }

    result
}

/// Multiply two polynomials (coefficient vectors).
pub fn poly_mul<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut result = vec![F::zero(); a.len() + b.len() - 1];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            result[i + j] += ai * bj;
        }
    }
    result
}

/// Add two polynomials (coefficient vectors), padding the shorter one.
pub fn poly_add<F: PrimeField>(a: &[F], b: &[F]) -> Vec<F> {
    let n = a.len().max(b.len());
    let mut result = vec![F::zero(); n];
    for (i, &ai) in a.iter().enumerate() {
        result[i] += ai;
    }
    for (i, &bi) in b.iter().enumerate() {
        result[i] += bi;
    }
    result
}

/// Polynomial long division: returns (quotient, remainder) such that f = q·g + r.
///
/// `g` must not be the zero polynomial.
pub fn poly_div_rem<F: PrimeField>(f: &[F], g: &[F]) -> (Vec<F>, Vec<F>) {
    let g_deg = g
        .iter()
        .rposition(|c| !c.is_zero())
        .expect("poly_div_rem: divisor must not be zero polynomial");

    let g_lead_inv = g[g_deg].inverse().expect("leading coefficient must be nonzero");

    let mut rem: Vec<F> = f.to_vec();
    while rem.last() == Some(&F::zero()) {
        rem.pop();
    }

    // deg(rem) < deg(g) → quotient is 0, remainder is f unchanged
    if rem.is_empty() || rem.len() <= g_deg {
        return (vec![], f.to_vec());
    }

    let quot_size = rem.len() - g_deg;
    let mut quotient = vec![F::zero(); quot_size];

    while rem.len() > g_deg {
        let rem_deg = rem.len() - 1;
        let coeff = rem[rem_deg] * g_lead_inv;
        let shift = rem_deg - g_deg;
        quotient[shift] = coeff;

        for k in 0..=g_deg {
            rem[shift + k] -= coeff * g[k];
        }

        while rem.last() == Some(&F::zero()) {
            rem.pop();
        }
    }

    (quotient, rem)
}

// ── Tests ──────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr as Fp;
    use crate::polynomial::evaluate_on_domain;

    fn add_gate() -> Gate<Fp> {
        Gate {
            q_l: Fp::from(1u64),
            q_r: Fp::from(1u64),
            q_m: Fp::from(0u64),
            q_o: -Fp::from(1u64),
            q_c: Fp::from(0u64),
        }
    }

    fn mul_gate() -> Gate<Fp> {
        Gate {
            q_l: Fp::from(0u64),
            q_r: Fp::from(0u64),
            q_m: Fp::from(1u64),
            q_o: -Fp::from(1u64),
            q_c: Fp::from(0u64),
        }
    }

    #[test]
    fn test_gate_addition() {
        // q_L·2 + q_R·3 + q_O·(-5) = 2 + 3 - 5 = 0
        let circuit = Circuit {
            gates: vec![add_gate()],
            a: vec![Fp::from(2u64)],
            b: vec![Fp::from(3u64)],
            c: vec![Fp::from(5u64)],
        };
        assert!(circuit.is_satisfied());
    }

    #[test]
    fn test_gate_multiplication() {
        // q_M·3·4 + q_O·(-12) = 12 - 12 = 0
        let circuit = Circuit {
            gates: vec![mul_gate()],
            a: vec![Fp::from(3u64)],
            b: vec![Fp::from(4u64)],
            c: vec![Fp::from(12u64)],
        };
        assert!(circuit.is_satisfied());
    }

    #[test]
    fn test_gate_unsatisfied() {
        // 2 + 3 ≠ 6
        let circuit = Circuit {
            gates: vec![add_gate()],
            a: vec![Fp::from(2u64)],
            b: vec![Fp::from(3u64)],
            c: vec![Fp::from(6u64)],
        };
        assert!(!circuit.is_satisfied());
    }

    #[test]
    fn test_quotient_poly_divides() {
        // Two satisfied addition gates over domain {1, 2}
        let circuit = Circuit {
            gates: vec![add_gate(), add_gate()],
            a: vec![Fp::from(2u64), Fp::from(10u64)],
            b: vec![Fp::from(3u64), Fp::from(20u64)],
            c: vec![Fp::from(5u64), Fp::from(30u64)],
        };
        let domain = vec![Fp::from(1u64), Fp::from(2u64)];
        assert!(circuit.is_satisfied());
        assert!(circuit.quotient_poly(&domain).is_some(), "satisfied circuit must have exact quotient");
    }

    #[test]
    fn test_quotient_poly_none() {
        // Single unsatisfied gate: 2 + 3 ≠ 6
        let circuit = Circuit {
            gates: vec![add_gate()],
            a: vec![Fp::from(2u64)],
            b: vec![Fp::from(3u64)],
            c: vec![Fp::from(6u64)],
        };
        let domain = vec![Fp::from(1u64)];
        assert!(!circuit.is_satisfied());
        assert!(circuit.quotient_poly(&domain).is_none(), "unsatisfied circuit must not have exact quotient");
    }

    #[test]
    fn test_grand_product_identity() {
        // Identity permutation: every wire maps to itself → all ratios = 1 → Z ≡ 1
        let n = 4usize;
        let circuit = Circuit {
            gates: (0..n).map(|_| Gate {
                q_l: Fp::from(1u64), q_r: Fp::from(0u64),
                q_m: Fp::from(0u64), q_o: Fp::from(0u64), q_c: Fp::from(0u64),
            }).collect(),
            a: (0..n).map(|i| Fp::from((i + 1) as u64)).collect(),
            b: (0..n).map(|i| Fp::from((n + i + 1) as u64)).collect(),
            c: (0..n).map(|i| Fp::from((2 * n + i + 1) as u64)).collect(),
        };

        // Full identity: σ_a[i]=i, σ_b[i]=n+i, σ_c[i]=2n+i
        let perm = PermutationArgument::<Fp>::new(
            (0..n).collect(),
            (n..2 * n).collect(),
            (2 * n..3 * n).collect(),
        );

        let beta = Fp::from(5u64);
        let gamma = Fp::from(7u64);

        let z = perm.grand_product(&circuit, beta, gamma);
        assert!(perm.check_grand_product(&z), "identity permutation → Z[n] must equal 1");
    }

    #[test]
    fn test_lagrange_interpolate() {
        // f(x) = x²: (1,1), (2,4), (3,9) → coefficients [0, 0, 1]
        let domain: Vec<Fp> = (1u64..=3).map(Fp::from).collect();
        let values: Vec<Fp> = vec![Fp::from(1u64), Fp::from(4u64), Fp::from(9u64)];
        let poly = lagrange_interpolate(&domain, &values);

        // Re-evaluate at the given points and check interpolation correctness
        let evals = evaluate_on_domain(&poly, &domain);
        for (i, (&got, &expected)) in evals.iter().zip(values.iter()).enumerate() {
            assert_eq!(got, expected, "lagrange eval mismatch at domain[{i}]");
        }
    }
}
