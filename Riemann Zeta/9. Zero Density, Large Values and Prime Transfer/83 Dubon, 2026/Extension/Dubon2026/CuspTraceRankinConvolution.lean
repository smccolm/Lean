import Dubon2026.CuspTraceCoefficients
import Dubon2026.RankinConvolutionEnergy

/-! # The genuine nonnegative dual Rankin convolution of a finite cusp trace -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

variable {N : ℕ} {H : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ H)]
  (hH : Gamma N ≤ H) {k : ℤ} (f : CuspForm (H.map (mapGL ℝ)) k)

/-- The true full-level square convolution of all actual normalized cusp-trace coefficients. -/
def cuspTraceRankinCoefficients : ℕ → ℂ :=
  LSeries.convolution (principalSquareCoefficients 1) (fun n => (cuspTraceSquareCoefficients hH f n : ℂ))

/-- The actual dual coefficient is the literal divisor-antidiagonal sum. -/
theorem cuspTraceRankinCoefficients_eq (n : ℕ) :
    cuspTraceRankinCoefficients hH f n = ∑ uv ∈ n.divisorsAntidiagonal,
      principalSquareCoefficients 1 uv.1 * (cuspTraceSquareCoefficients hH f uv.2 : ℂ) :=
  by rw [cuspTraceRankinCoefficients, LSeries.convolution_def]

/-- The zero coefficient of the actual trace convolution vanishes. -/
theorem cuspTraceRankinCoefficients_zero : cuspTraceRankinCoefficients hH f 0 = 0 :=
  LSeries.convolution_map_zero _ _

/-- The actual convolution coefficients have nonnegative real parts. -/
theorem cuspTraceRankinCoefficients_re_nonneg (n : ℕ) :
    0 ≤ (cuspTraceRankinCoefficients hH f n).re := by
  rw [cuspTraceRankinCoefficients_eq, Complex.re_sum]
  apply Finset.sum_nonneg
  intro uv _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (principalSquareCoefficients_re_nonneg 1 uv.1)
    (cuspTraceSquareCoefficients_nonneg hH f uv.2)

/-- The actual convolution coefficients are real, not merely bounded by a positive majorant. -/
theorem cuspTraceRankinCoefficients_im (n : ℕ) : (cuspTraceRankinCoefficients hH f n).im = 0 := by
  rw [cuspTraceRankinCoefficients_eq, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro uv _
  simp only [Complex.mul_im, principalSquareCoefficients_im, Complex.ofReal_im, zero_mul, mul_zero, add_zero]

/-- Real parts commute with this genuine nonnegative convolution. -/
theorem cuspTraceRankin_re_eq_convolution (n : ℕ) :
    (cuspTraceRankinCoefficients hH f n).re =
      LSeries.convolution (fun d => (principalSquareCoefficients 1 d).re)
        (cuspTraceSquareCoefficients hH f) n := by
  rw [cuspTraceRankinCoefficients_eq, LSeries.convolution_def, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro uv _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- The actual dual coefficients satisfy the linear mean needed for the sharp Riesz kernel estimates. -/
theorem exists_cuspTraceRankin_sum_upper [NeZero N] (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.Icc 1 X, (cuspTraceRankinCoefficients hH f n).re) ≤ C * X := by
  obtain ⟨B, hB, hb⟩ := exists_cuspTraceSquare_sum_upper hH f hk
  let S : ℝ := ∑' n : ℕ, (principalSquareCoefficients 1 n).re / (n : ℝ)
  have hS : 0 ≤ S := tsum_nonneg (fun n => div_nonneg
    (principalSquareCoefficients_re_nonneg 1 n) (Nat.cast_nonneg n))
  refine ⟨B * (S + 1), mul_pos hB (by linarith), fun X => ?_⟩
  simp_rw [cuspTraceRankin_re_eq_convolution]
  have hh := sum_convolution_le_linear (principalSquareCoefficients_re_nonneg 1) hB.le hb
    (principalSquare_reciprocal_summable 1) X
  change _ ≤ B * (S + 1) * X
  change _ ≤ B * X * S at hh
  nlinarith [Nat.cast_nonneg (α := ℝ) X]

/-- The actual dual Rankin Dirichlet series is absolutely convergent throughout Re(s)>1. -/
theorem cuspTraceRankin_lseriesSummable [NeZero N] (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (cuspTraceRankinCoefficients hH f) s :=
  (principalSquare_lseriesSummable 1 (by linarith)).convolution (cuspTraceSquare_lseriesSummable hH f hk hs)

/-- Its exact Dirichlet-series identity retains the full-level principal square factor and every cusp in the trace. -/
theorem cuspTraceRankin_LSeries [NeZero N] (hk : 0 < k) {s : ℂ} (hs : 1 < s.re) :
    LSeries (cuspTraceRankinCoefficients hH f) s =
      DirichletCharacter.LFunctionTrivChar 1 (2 * s) *
        ∑ q : SL(2, ℤ) ⧸ H, cuspPeriodRankinSeries (cuspCosetFamily hH f q) N s := by
  rw [cuspTraceRankinCoefficients, LSeries_convolution'
    (principalSquare_lseriesSummable 1 (by linarith)) (cuspTraceSquare_lseriesSummable hH f hk hs),
    principalSquare_LSeries 1 (by linarith), cuspTraceSquare_LSeries hH f hk hs]

end
end Dubon2026
