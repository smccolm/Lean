import GafniTao.SharpPerronEndpoint

/-!
# Global sharp Perron error identity

This file passes from the termwise cutoff errors to the norm of the complete
von Mangoldt series.  The right side is still the exact summable error series;
its subsequent dyadic estimate is a separate arithmetic step.
-/

namespace GafniTao

/-- Absolute summability of the exact cutoff-error series. -/
theorem summable_norm_vonMangoldt_sharpPerron_cutoffError
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    Summable (fun n : ℕ =>
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
            sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
            sharpPerronCutoff x n‖) := by
  exact ((summable_vonMangoldt_mul_sharpPerronKernel hc hx).sub
    (summable_vonMangoldt_mul_sharpPerronCutoff hx.le)).norm

/-- The right-line Perron approximation error is bounded by the sum of the
exact termwise cutoff errors. -/
theorem norm_sharpPerron_logDerivative_sub_psi_le_tsum_termErrors
    {c T x : ℝ} (hc : 1 < c) (hx : 0 < x) :
    ‖(1 / (2 * Real.pi) : ℂ) *
          (∫ t in (-T)..T,
            (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I) /
                riemannZeta ((c : ℂ) + (t : ℂ) * Complex.I)) *
              (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) /
                ((c : ℂ) + (t : ℂ) * Complex.I)) -
        (Chebyshev.psi x : ℂ)‖ ≤
      ∑' n : ℕ,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
              sharpPerronKernel c T x n -
          (ArithmeticFunction.vonMangoldt n : ℂ) *
              sharpPerronCutoff x n‖ := by
  rw [sharpPerron_logDerivative_sub_psi_eq_tsum_cutoffError hc hx]
  exact norm_tsum_le_tsum_norm
    (summable_norm_vonMangoldt_sharpPerron_cutoffError hc hx)

end GafniTao
