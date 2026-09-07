import GafniTao.FordPositiveExplicitIdentity

open GafniTao

noncomputable section

set_option maxRecDepth 100000000
set_option maxHeartbeats 0

theorem probe_fordBiIntegralPolynomial_coeff_succ
    (p : FordBiPolynomial) (n : ℕ) :
    (fordBiIntegralPolynomial p).coeff (n + 1) =
      Polynomial.C (1 / (n + 1 : ℚ)) * p.coeff n := by
  have h := congrArg (fun q : FordBiPolynomial => q.coeff n)
    (derivative_fordBiIntegralPolynomial p)
  simp only [Polynomial.coeff_derivative] at h
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  calc
    (fordBiIntegralPolynomial p).coeff (n + 1) =
        Polynomial.C (1 / ((n : ℚ) + 1)) *
          (Polynomial.C ((n : ℚ) + 1) *
            (fordBiIntegralPolynomial p).coeff (n + 1)) := by
          rw [← Polynomial.C_mul]
          field_simp
    _ = Polynomial.C (1 / (n + 1 : ℚ)) * p.coeff n := by
      rw [h]

example :
    fordBiIntegralPolynomial fordNegativeUpperPolynomial =
      fordNegativePrimitiveExplicit := by
  rw [fordNegativeUpperPolynomial_eq_explicit]
  apply Polynomial.ext
  intro n
  cases n with
  | zero =>
      simp [fordNegativePrimitiveExplicit, fordNegativePrimitiveBlock0,
        fordNegativePrimitiveBlock1, fordNegativePrimitiveBlock2]
  | succ n =>
      rw [show n + 1 = Nat.succ n by omega,
        probe_fordBiIntegralPolynomial_coeff_succ]
      by_cases hn : n < 55
      · interval_cases n <;>
          simp only [fordNegativePrimitiveExplicit,
            fordNegativePrimitiveBlock0, fordNegativePrimitiveBlock1,
            fordNegativePrimitiveBlock2, fordNegativeUpperExplicit,
            fordNegativeUpperBlock0, fordNegativeUpperBlock1,
            fordNegativeUpperBlock2, Polynomial.coeff_add,
            Polynomial.coeff_C_mul_X_pow] <;>
          norm_num
      · have hn' : 55 ≤ n := by omega
        have hupper : fordNegativeUpperExplicit.coeff n = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have hdegree : fordNegativeUpperExplicit.natDegree ≤ 54 := by
            unfold fordNegativeUpperExplicit fordNegativeUpperBlock0
              fordNegativeUpperBlock1 fordNegativeUpperBlock2
            compute_degree
          omega
        have hprimitive :
            fordNegativePrimitiveExplicit.coeff (n + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have hdegree : fordNegativePrimitiveExplicit.natDegree ≤ 55 := by
            unfold fordNegativePrimitiveExplicit fordNegativePrimitiveBlock0
              fordNegativePrimitiveBlock1 fordNegativePrimitiveBlock2
            compute_degree
          omega
        rw [hupper, hprimitive]
        simp
