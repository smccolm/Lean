import Dubon2026.GammaRieszDualSplit
import Dubon2026.RankinConvolutionPowerBounds
import Dubon2026.RankinConvolutionMean

/-! # The genuine Rankin convolution dual Gamma series -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup

noncomputable section

/-- The actual Rankin coefficient series with the Gamma parameter fixed to the cusp form's own weight. -/
def rankinGammaDualSeries {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A x : ℝ) : ℂ :=
  gammaRieszDualSeries (fun n => (rankinConvolutionCoefficients f n).re) k A x

/-- The actual series has precisely the complex Rankin coefficients and reciprocal positive-index factor. -/
theorem rankinGammaDualSeries_eq {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (A x : ℝ) :
    rankinGammaDualSeries f A x = ∑' n : ℕ,
      (rankinConvolutionCoefficients f n / (n : ℂ)) *
        ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (A * n * x)) := by
  unfold rankinGammaDualSeries gammaRieszDualSeries
  apply tsum_congr
  intro n
  simp only [gammaRieszDualTerm, Complex.ofReal_div, Complex.ofReal_natCast,
    rankinConvolutionCoefficients_ofReal_re]

/-- Absolute convergence of the genuine Rankin Gamma series consumes the actual coefficient mean. -/
theorem summable_norm_rankinGammaDualTerm {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    Summable (fun n : ℕ => ‖(rankinConvolutionCoefficients f n / (n : ℂ)) *
      ((x : ℂ) ^ 2 * gammaRieszKernel (k : ℝ) 2 (A * n * x))‖) := by
  obtain ⟨B, hB, hb⟩ := exists_rankinConvolution_sum_upper f (by omega)
  have hc0 : (rankinConvolutionCoefficients f 0).re = 0 := by simp [rankinConvolutionCoefficients_zero]
  have hb' (N : ℕ) : (∑ n ∈ Finset.Icc 0 N, (rankinConvolutionCoefficients f n).re) ≤ B * N := by
    rw [sum_Icc_zero_eq_positive hc0]
    exact hb N
  have hs := summable_norm_gammaRieszDualTerm (by exact_mod_cast hk : (2 : ℝ) ≤ k)
    hA (rankinConvolutionCoefficients_re_nonneg f) hB.le hb' hx
  simpa only [gammaRieszDualTerm, Complex.ofReal_div, Complex.ofReal_natCast,
    rankinConvolutionCoefficients_ofReal_re] using hs

/-- The actual Rankin Gamma series has both sharp contributions to its second difference, with no arithmetic premise left to the caller. -/
theorem exists_rankinGammaDualSeries_difference_bound {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 2 ≤ k) {A : ℝ} (hA : 0 < A) :
    ∃ C₀ C₂ : ℝ, 0 < C₀ ∧ 0 < C₂ ∧ ∀ (x h : ℝ) (N : ℕ), 0 < x → 0 ≤ h → h ≤ x → 1 ≤ N →
      ‖rankinGammaDualSeries f A (x + 2 * h) - 2 * rankinGammaDualSeries f A (x + h) +
        rankinGammaDualSeries f A x‖ ≤
        C₀ * h ^ 2 * x ^ (3 / 8 : ℝ) * (N : ℝ) ^ (3 / 8 : ℝ) +
        C₂ * x ^ (15 / 8 : ℝ) * (N : ℝ) ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := exists_rankinConvolution_sum_upper f (by omega)
  have hc0 : (rankinConvolutionCoefficients f 0).re = 0 := by simp [rankinConvolutionCoefficients_zero]
  have hb' (N : ℕ) : (∑ n ∈ Finset.Icc 0 N, (rankinConvolutionCoefficients f n).re) ≤ B * N := by
    rw [sum_Icc_zero_eq_positive hc0]
    exact hb N
  obtain ⟨C, hC, hpower⟩ := exists_rankinConvolution_power_bounds f (by omega)
  obtain ⟨L, H, hL, hH, hsplit⟩ := exists_gammaRieszDualSeries_split_bound
    (by exact_mod_cast hk : (2 : ℝ) ≤ k) hA
  refine ⟨L * C, H * C, mul_pos hL hC, mul_pos hH hC, ?_⟩
  intro x h N hx hh hhx hN
  have hbnd := hsplit (fun n => (rankinConvolutionCoefficients f n).re) B
    (rankinConvolutionCoefficients_re_nonneg f) hB.le hb' x h N hx hh hhx hN
  have hp := hpower N hN
  apply hbnd.trans
  have hlow := mul_le_mul_of_nonneg_left hp.1
    (show 0 ≤ L * h ^ 2 * x ^ (3 / 8 : ℝ) by positivity)
  have hhigh := mul_le_mul_of_nonneg_left hp.2.2
    (show 0 ≤ H * x ^ (15 / 8 : ℝ) by positivity)
  convert add_le_add hlow hhigh using 1 <;> ring

end
end Dubon2026
