import TaoTrudgianYang2025.BetaMorseChangeVariables

/-!
# The original cutoff in the actual quadratic-coordinate amplitude

The weight is the original Poisson cutoff composed with the actual
inverse, multiplied by its Jacobian. Its value at zero keeps that
cutoff; no slope-chart cutoff or uncut amplitude is substituted.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseMorseAmplitude (χ F : ℝ → ℝ) (v z : ℝ) : ℝ :=
  χ (modelPhaseMorseInverse F v z)*deriv (modelPhaseMorseInverse F v) z

theorem modelPhaseMorseAmplitude_contDiffAt
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hχ : ContDiff ℝ ∞ χ)
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v) :
    ContDiffAt ℝ ∞ (modelPhaseMorseAmplitude χ F v) z := by
  have hi := modelPhaseMorseInverse_contDiffAt hσ hδ hF hv hz
  exact (hχ.contDiffAt.comp z hi).mul (hi.derivWithin (by simp))

theorem modelPhaseMorseAmplitude_zero
    {χ F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseMorseAmplitude χ F v 0 =
      χ (modelPhaseInverseSlope F v)*modelPhaseStationaryAmplitude F v := by
  rw [modelPhaseMorseAmplitude,modelPhaseMorseInverse_zero hσ hδ hF hv,
    (modelPhaseMorseInverse_hasDerivAt_zero hσ hδ hF hv).deriv]

theorem abs_modelPhaseMorseAmplitude_le
    {χ F : ℝ → ℝ} {σ δ v z M : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hM : 0 ≤ M) (hχ : ∀ u ∈ Ioo (1 : ℝ) 2, |χ u| ≤ M) :
    |modelPhaseMorseAmplitude χ F v z| ≤ M*(Real.sqrt (σ+1)/modelPhaseCurvatureLower σ) := by
  rw [modelPhaseMorseAmplitude,abs_mul,
    abs_of_pos (modelPhaseMorseInverse_deriv_pos hσ hδ hF hv hz)]
  exact mul_le_mul (hχ _ (modelPhaseMorseInverse_mem hz))
    (modelPhaseMorseInverse_deriv_bounds hσ hδ hF hv hz).2
    (modelPhaseMorseInverse_deriv_pos hσ hδ hF hv hz).le hM

theorem modelPhaseMorseAmplitude_nonneg
    {χ F : ℝ → ℝ} {σ δ v z : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hz : z ∈ modelPhaseMorseRange F v)
    (hχ : ∀ u ∈ Ioo (1 : ℝ) 2, 0 ≤ χ u) :
    0 ≤ modelPhaseMorseAmplitude χ F v z :=
  mul_nonneg (hχ _ (modelPhaseMorseInverse_mem hz))
    (modelPhaseMorseInverse_deriv_pos hσ hδ hF hv hz).le

end TaoTrudgianYang2025

