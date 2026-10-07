import Dubon2026.GammaRieszBounds

/-! # Quantitative truncation errors for the actual improper Riesz Gamma kernels -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology ComplexConjugate

noncomputable section

/-- The actual positive-half improper integral has an explicit inverse-square-root truncation error. -/
theorem norm_gammaRieszPositiveIntegral_sub_cutoff_le {k r x T : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : gammaRieszTailHeight k x ≤ T) :
    ‖gammaRieszPositiveIntegral k r x - ∫ t in 0..T, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r / Real.sqrt T := by
  have hc := continuous_gammaRieszIntegrand hk hr0 hr2 hx
  apply le_of_tendsto ((tendsto_gammaRieszPositiveIntegral hk hr0 hr2 hx).sub tendsto_const_nhds).norm
  filter_upwards [eventually_ge_atTop T] with u hu
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 T)
    (hc.intervalIntegrable T u), add_sub_cancel_left]
  exact norm_gammaRieszIntegrand_tail_le hk hr0 hr2 hx hT hu

/-- The literal symmetric cutoff approximates the genuine normalized kernel with an explicit error. -/
theorem norm_gammaRieszKernel_sub_cutoff_le {k r x T : ℝ}
    (hk : 2 ≤ k) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hx : 0 < x)
    (hT : gammaRieszTailHeight k x ≤ T) :
    ‖gammaRieszKernel k r x - (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, gammaRieszIntegrand k r x t‖ ≤
      4 * gammaRieszConstant k r * x ^ gammaRieszLine r / (Real.pi * Real.sqrt T) := by
  have hh := norm_gammaRieszPositiveIntegral_sub_cutoff_le hk hr0 hr2 hx hT
  have he : gammaRieszKernel k r x - (1 / (2 * Real.pi) : ℝ) • ∫ t in -T..T, gammaRieszIntegrand k r x t =
      (1 / (2 * Real.pi) : ℝ) •
        ((gammaRieszPositiveIntegral k r x - ∫ t in 0..T, gammaRieszIntegrand k r x t) +
          conj (gammaRieszPositiveIntegral k r x - ∫ t in 0..T, gammaRieszIntegrand k r x t)) := by
    rw [gammaRieszKernel, gammaRiesz_symmetric_integral_eq hk hr0 hr2 hx, map_sub, ← smul_sub]
    congr 1
    abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (1 / (2 * Real.pi) : ℝ))]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (‖gammaRieszPositiveIntegral k r x - ∫ t in 0..T, gammaRieszIntegrand k r x t‖ +
          ‖conj (gammaRieszPositiveIntegral k r x - ∫ t in 0..T, gammaRieszIntegrand k r x t)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ (1 / (2 * Real.pi)) * (2 * (4 * gammaRieszConstant k r * x ^ gammaRieszLine r / Real.sqrt T)) := by
      rw [norm_conj]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

end
end Dubon2026
