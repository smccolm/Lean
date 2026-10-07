import Dubon2026.MoebiusSquareSeries
import Dubon2026.RankinConvolution

/-! # Exact inversion of the genuine Rankin convolution coefficients -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup Filter

noncomputable section

/-- The inverse square convolution is an actual absolutely convergent L-series in Re(s)>1. -/
theorem rankin_deconvolution_lseriesSummable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (LSeries.convolution (moebiusSquareCoefficients Q)
      (rankinConvolutionCoefficients f)) s :=
  (moebiusSquare_lseriesSummable Q (by linarith)).convolution
    (rankinConvolution_lseriesSummable f hk hs)

/-- Möbius inversion cancels the actual principal-character L-factor. -/
theorem rankin_deconvolution_LSeries {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    LSeries (LSeries.convolution (moebiusSquareCoefficients Q)
      (rankinConvolutionCoefficients f)) s = cuspRankinSeries f s := by
  rw [LSeries_convolution' (moebiusSquare_lseriesSummable Q (by linarith))
    (rankinConvolution_lseriesSummable f hk hs), rankinConvolution_LSeries f hk hs,
    ← principalSquare_LSeries Q (by linarith), ← mul_assoc,
    mul_comm (LSeries (moebiusSquareCoefficients Q) s),
    principalSquare_mul_moebiusSquare_LSeries Q (by linarith), one_mul]

/-- Uniqueness of genuine absolutely convergent Dirichlet series gives the exact coefficient inversion at every index. -/
theorem rankin_deconvolution_coefficients {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) (n : ℕ) :
    LSeries.convolution (moebiusSquareCoefficients Q) (rankinConvolutionCoefficients f) n =
      ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [normalizedCuspCoefficients, shiftedCoefficients, cuspCoefficients_zero]
  apply LSeries.eq_of_LSeries_eventually_eq
    ((rankin_deconvolution_lseriesSummable f hk (s := 2) (by norm_num)).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _))
    ((normalized_cusp_square_lseries_summable f hk (s := 2) (by norm_num)).abscissaOfAbsConv_le.trans_lt
      (EReal.coe_lt_top _)) _ hn
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact rankin_deconvolution_LSeries f hk hx

/-- The true normalized coefficient squares are the finite divisor-antidiagonal Möbius inversion of the completed convolution. -/
theorem normalized_cusp_square_eq_moebius_convolution {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k) (n : ℕ) :
    ((‖normalizedCuspCoefficients f n‖ ^ 2 : ℝ) : ℂ) =
      ∑ uv ∈ n.divisorsAntidiagonal, moebiusSquareCoefficients Q uv.1 *
        rankinConvolutionCoefficients f uv.2 := by
  rw [← rankin_deconvolution_coefficients f hk n, LSeries.convolution_def]

end
end Dubon2026
