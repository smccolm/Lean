import GafniTao.FordPositiveExplicitIdentity

/-!
# Outer-variable coefficient formula for Ford's negative primitive

This is the exact coefficientwise antiderivative identity used to connect the
negative compact integral to its independently generated rational certificate.
-/

namespace GafniTao

noncomputable section

theorem fordBiIntegralPolynomial_coeff_succ
    (p : FordBiPolynomial) (n : ℕ) :
    (fordBiIntegralPolynomial p).coeff (n + 1) =
      Polynomial.C (1 / (n + 1 : ℚ)) * p.coeff n := by
  have h := congrArg (fun q : FordBiPolynomial => q.coeff n)
    (derivative_fordBiIntegralPolynomial p)
  simp only [Polynomial.coeff_derivative] at h
  have hn : ((n : ℚ) + 1) ≠ 0 := by positivity
  rw [← h]
  rw [show (n : Polynomial ℚ) + 1 =
    Polynomial.C ((n : ℚ) + 1) by norm_num]
  rw [mul_comm ((fordBiIntegralPolynomial p).coeff (n + 1))
      (Polynomial.C ((n : ℚ) + 1)),
    ← mul_assoc, ← Polynomial.C_mul]
  field_simp
  simp

end

end GafniTao
