import Dubon2026.PrincipalSquareSeries
import Dubon2026.CuspRankinSeries

/-! # The genuine nonnegative Rankin convolution coefficients -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual square-supported principal coefficient convolution with normalized cusp coefficient squares. -/
def rankinConvolutionCoefficients {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : ℕ → ℂ :=
  LSeries.convolution (principalSquareCoefficients Q)
    (fun n => ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ))

/-- The true Rankin convolution is the literal finite divisor-antidiagonal sum. -/
theorem rankinConvolutionCoefficients_eq {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    rankinConvolutionCoefficients f n =
      ∑ uv ∈ n.divisorsAntidiagonal, principalSquareCoefficients Q uv.1 *
        ((‖normalizedCuspCoefficients f uv.2‖ ^ 2 : ℝ) : ℂ) := by
  rw [rankinConvolutionCoefficients, LSeries.convolution_def]

/-- The actual convolution has zero coefficient at zero. -/
theorem rankinConvolutionCoefficients_zero {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : rankinConvolutionCoefficients f 0 = 0 :=
  LSeries.convolution_map_zero _ _

/-- Every actual Rankin convolution coefficient has nonnegative real part. -/
theorem rankinConvolutionCoefficients_re_nonneg {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    0 ≤ (rankinConvolutionCoefficients f n).re := by
  rw [rankinConvolutionCoefficients_eq, Complex.re_sum]
  apply Finset.sum_nonneg
  intro uv huv
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (principalSquareCoefficients_re_nonneg Q uv.1) (sq_nonneg _)

/-- Every actual Rankin convolution coefficient is real. -/
theorem rankinConvolutionCoefficients_im {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (n : ℕ) :
    (rankinConvolutionCoefficients f n).im = 0 := by
  rw [rankinConvolutionCoefficients_eq, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro uv huv
  simp only [Complex.mul_im, principalSquareCoefficients_im, Complex.ofReal_im,
    zero_mul, mul_zero, add_zero]

/-- The actual convolution Dirichlet series is absolutely convergent in Re(s)>1. -/
theorem rankinConvolution_lseriesSummable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (rankinConvolutionCoefficients f) s :=
  (principalSquare_lseriesSummable Q (by linarith)).convolution
    (normalized_cusp_square_lseries_summable f hk hs)

/-- The true convolution series is exactly L(2s,chi_0) times the actual normalized square series. -/
theorem rankinConvolution_LSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeries (rankinConvolutionCoefficients f) s =
      DirichletCharacter.LFunctionTrivChar Q (2 * s) * cuspRankinSeries f s := by
  rw [rankinConvolutionCoefficients, LSeries_convolution'
    (principalSquare_lseriesSummable Q (by linarith))
    (normalized_cusp_square_lseries_summable f hk hs), principalSquare_LSeries Q (by linarith)]
  rfl

end
end Dubon2026
