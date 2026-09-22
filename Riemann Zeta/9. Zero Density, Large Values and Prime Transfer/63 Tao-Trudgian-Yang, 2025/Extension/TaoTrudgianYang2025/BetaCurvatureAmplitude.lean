import TaoTrudgianYang2025.BetaStationarySum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Actual curvature amplitudes for the model-phase B transformation

The amplitude is the inverse square root of the original curvature at
the actual inverse-slope point. Positivity, uniform bounds, smoothness
and physical N/sqrt(T) normalization are derived from the source model.
No stationary integral approximation is asserted.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

def modelPhaseCurvatureAt (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  -deriv (deriv F) (modelPhaseInverseSlope F v)

def modelPhaseStationaryAmplitude (F : ℝ → ℝ) (v : ℝ) : ℝ :=
  (Real.sqrt (modelPhaseCurvatureAt F v))⁻¹

theorem modelPhaseCurvatureAt_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseCurvatureLower σ ≤ modelPhaseCurvatureAt F v ∧
      modelPhaseCurvatureAt F v ≤ σ+1 :=
  approximateModelPhase_curvature_deriv_bounds hσ hδ hF (modelPhaseInverseSlope_mem hv)

theorem modelPhaseCurvatureAt_pos {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    0 < modelPhaseCurvatureAt F v :=
  (modelPhaseCurvatureLower_pos hσ).trans_le (modelPhaseCurvatureAt_bounds hσ hδ hF hv).1

theorem modelPhaseStationaryAmplitude_pos {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    0 < modelPhaseStationaryAmplitude F v :=
  inv_pos.mpr (Real.sqrt_pos.mpr (modelPhaseCurvatureAt_pos hσ hδ hF hv))

theorem modelPhaseStationaryAmplitude_bounds {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    (Real.sqrt (σ+1))⁻¹ ≤ modelPhaseStationaryAmplitude F v ∧
      modelPhaseStationaryAmplitude F v ≤ (Real.sqrt (modelPhaseCurvatureLower σ))⁻¹ := by
  have hb := modelPhaseCurvatureAt_bounds hσ hδ hF hv
  exact ⟨inv_anti₀ (Real.sqrt_pos.mpr (modelPhaseCurvatureAt_pos hσ hδ hF hv))
    (Real.sqrt_le_sqrt hb.2),
    inv_anti₀ (Real.sqrt_pos.mpr (modelPhaseCurvatureLower_pos hσ))
      (Real.sqrt_le_sqrt hb.1)⟩

theorem modelPhaseCurvatureAt_contDiffAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseCurvatureAt F) v := by
  have hd : ContDiffAt ℝ ∞ (deriv (deriv F)) (modelPhaseInverseSlope F v) :=
    (approximateModelPhase_deriv_contDiffAt hF (modelPhaseInverseSlope_mem hv)).derivWithin
      (by simp)
  exact (hd.comp v (modelPhaseInverseSlope_contDiffAt hσ hδ hF hv)).neg

theorem modelPhaseStationaryAmplitude_contDiffAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffAt ℝ ∞ (modelPhaseStationaryAmplitude F) v := by
  have hp := modelPhaseCurvatureAt_pos hσ hδ hF hv
  exact ((modelPhaseCurvatureAt_contDiffAt hσ hδ hF hv).sqrt hp.ne').inv
    (Real.sqrt_pos.mpr hp).ne'

theorem modelPhaseCurvatureAt_hasDerivAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseCurvatureAt F)
      (deriv (deriv (deriv F)) (modelPhaseInverseSlope F v) /
        modelPhaseCurvatureAt F v) v := by
  have hd : ContDiffAt ℝ ∞ (deriv (deriv F)) (modelPhaseInverseSlope F v) :=
    (approximateModelPhase_deriv_contDiffAt hF (modelPhaseInverseSlope_mem hv)).derivWithin
      (by simp)
  have hi := (modelPhaseInverseSlope_hasStrictDerivAt hσ hδ hF hv).hasDerivAt
  convert ((hd.differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.comp v hi).neg using 1
  simp only [modelPhaseCurvatureAt,div_eq_mul_inv]
  ring

theorem modelPhaseStationaryAmplitude_hasDerivAt {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {v : ℝ} (hv : v ∈ modelPhaseSlopeRange F) :
    HasDerivAt (modelPhaseStationaryAmplitude F)
      (-deriv (deriv (deriv F)) (modelPhaseInverseSlope F v) /
        (2*(modelPhaseCurvatureAt F v)^2*Real.sqrt (modelPhaseCurvatureAt F v))) v := by
  have hp := modelPhaseCurvatureAt_pos hσ hδ hF hv
  have hs := Real.sqrt_pos.mpr hp
  have he := Real.sq_sqrt hp.le
  convert ((modelPhaseCurvatureAt_hasDerivAt hσ hδ hF hv).sqrt hp.ne').inv hs.ne' using 1
  field_simp
  rw [he]

theorem modelPhaseStationaryPoint_amplitude_scale
    {σ δ T N r : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange F) :
    (Real.sqrt (-deriv (deriv (modelPhaseFrequencyPhase F T N r))
      (modelPhaseStationaryPoint F T N r)))⁻¹ =
        (N/Real.sqrt T)*modelPhaseStationaryAmplitude F (r*N/T) := by
  have hx : modelPhaseStationaryPoint F T N r / N ∈ Ioo (1 : ℝ) 2 := by
    rw [modelPhaseStationaryPoint_div hN.ne']
    exact modelPhaseInverseSlope_mem hv
  rw [modelPhaseFrequencyPhase_secondDeriv hF hx,modelPhaseStationaryPoint_div hN.ne',
    show -(T/N^2*deriv (deriv F) (modelPhaseInverseSlope F (r*N/T))) =
      (T/N^2)*modelPhaseCurvatureAt F (r*N/T) by simp only [modelPhaseCurvatureAt,mul_neg],
    Real.sqrt_mul (div_nonneg hT.le (sq_nonneg N)),Real.sqrt_div hT.le,
    Real.sqrt_sq_eq_abs,abs_of_pos hN]
  unfold modelPhaseStationaryAmplitude
  field_simp

end TaoTrudgianYang2025
