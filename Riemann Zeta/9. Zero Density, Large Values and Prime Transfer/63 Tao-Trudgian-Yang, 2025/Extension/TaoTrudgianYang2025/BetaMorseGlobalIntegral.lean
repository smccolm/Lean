import TaoTrudgianYang2025.BetaMorseSupport
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Whole-line quadratic integrals with the actual smooth source weight

The extended weight is genuinely compactly supported and smooth.
The whole-line integral is exactly the prior integral over the moving image.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

def modelPhaseMorseSchwartz
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) : SchwartzMap ℝ ℝ :=
  (modelPhaseMorseWeight_hasCompactSupport hs hσ hδ hF hv).toSchwartzMap
    (modelPhaseMorseWeight_contDiff hχ hs hσ hδ hF hv)

theorem modelPhaseMorseSchwartz_apply
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (z : ℝ) :
    modelPhaseMorseSchwartz hχ hs hσ hδ hF hv z = modelPhaseMorseWeight χ F v z := rfl

theorem modelPhaseMorseWeightedIntegral_eq_global
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    modelPhaseMorseWeightedIntegral χ F T v =
      ∫ z : ℝ, (modelPhaseMorseWeight χ F v z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ) := by
  rw [modelPhaseMorseWeightedIntegral,
    ← integral_indicator (modelPhaseMorseRange_isOpen hσ hδ hF hv).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ modelPhaseMorseRange F v
  · rw [Set.indicator_of_mem hz,modelPhaseMorseWeight_eq hz]
  · rw [Set.indicator_of_notMem hz,modelPhaseMorseWeight_zero_of_not_mem hz,
      Complex.ofReal_zero,zero_mul]

theorem modelPhaseMorseGlobalIntegrand_integrable
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : Continuous χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (T : ℝ) :
    Integrable (fun z : ℝ => (modelPhaseMorseWeight χ F v z : ℂ)*
      (𝐞 (-(T/2)*z^2) : ℂ)) := by
  have h := (integrable_indicator_iff
    (modelPhaseMorseRange_isOpen hσ hδ hF hv).measurableSet).mpr
      (modelPhaseMorseWeightedIntegrand_integrableOn hχ hσ hδ hF hv T)
  apply h.congr
  filter_upwards [] with z
  by_cases hz : z ∈ modelPhaseMorseRange F v
  · rw [Set.indicator_of_mem hz,modelPhaseMorseWeight_eq hz]
  · rw [Set.indicator_of_notMem hz,modelPhaseMorseWeight_zero_of_not_mem hz,
      Complex.ofReal_zero,zero_mul]

theorem modelPhaseFourierMode_eq_global_morse
    {χ F : ℝ → ℝ} {σ δ T N r : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : T ≠ 0) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    modelPhaseFourierMode χ F T N r =
      (N : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ)*
        ∫ z : ℝ, (modelPhaseMorseWeight χ F (r*N/T) z : ℂ)*(𝐞 (-(T/2)*z^2) : ℂ) := by
  rw [modelPhaseFourierMode_morse hs hσ hδ hF hT hN hv,
    modelPhaseMorseWeightedIntegral_eq_global hσ hδ hF hv]

theorem modelPhaseMorseWeight_deriv_support
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (k : ℕ) :
    tsupport (iteratedDeriv k (modelPhaseMorseWeight χ F v)) ⊆
      modelPhaseMorseCoordinate F v '' tsupport χ := by
  induction k with
  | zero => exact modelPhaseMorseWeight_tsupport_subset hs hσ hδ hF hv
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

theorem modelPhaseMorseWeight_iteratedDeriv_integrable
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (k : ℕ) :
    Integrable (iteratedDeriv k (modelPhaseMorseWeight χ F v)) := by
  have hc : HasCompactSupport (iteratedDeriv k (modelPhaseMorseWeight χ F v)) :=
    (isCompact_modelPhaseMorseCoordinate_image_tsupport hs hσ hδ hF hv).of_isClosed_subset
      (isClosed_tsupport _) (modelPhaseMorseWeight_deriv_support hs hσ hδ hF hv k)
  exact ((modelPhaseMorseWeight_contDiff hχ hs hσ hδ hF hv).continuous_iteratedDeriv k
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).integrable_of_hasCompactSupport hc

end TaoTrudgianYang2025
