import TaoTrudgianYang2025.BetaTaylorIdentity

/-!
# Averaged curvature removes the quadratic coordinate's singularity

The actual stationary deficit is exactly a squared displacement times
a smooth positive average of the original curvature. This proves
smoothness through the critical point, not just away from it.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

def modelPhaseAveragedCurvature (F : ℝ → ℝ) (v u : ℝ) : ℝ :=
  -2*segmentTaylorAverage (deriv (deriv F)) (modelPhaseInverseSlope F v) 0 u

theorem modelPhaseAveragedCurvature_at_inverse (F : ℝ → ℝ) (v : ℝ) :
    modelPhaseAveragedCurvature F v (modelPhaseInverseSlope F v) =
      modelPhaseCurvatureAt F v := by
  rw [modelPhaseAveragedCurvature,segmentTaylorAverage_at_center]
  unfold modelPhaseCurvatureAt
  ring

theorem modelPhaseAveragedCurvature_contDiffAt
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (modelPhaseAveragedCurvature F v) u := by
  have hj : ∀ x ∈ Ioo (1 : ℝ) 2, ContDiffAt ℝ ∞ (deriv (deriv F)) x := by
    intro x hx
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      approximateModelPhase_iteratedDeriv_contDiffAt hF hx 2
  exact contDiffAt_const.mul ((segmentTaylorAverage_contDiffOn hj
    (modelPhaseInverseSlope_mem hv) 0).contDiffAt (isOpen_Ioo.mem_nhds hu))

theorem modelPhaseStationaryDeficit_eq_averagedCurvature
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseStationaryDeficit F v u =
      (u-modelPhaseInverseSlope F v)^2/2*modelPhaseAveragedCurvature F v u := by
  have h := segmentTaylorAverage_second (fun x hx => approximateModelPhase_contDiffAt hF hx)
    (modelPhaseInverseSlope_mem hv) hu
  rw [deriv_modelPhaseInverseSlope_apply hv] at h
  unfold modelPhaseStationaryDeficit modelPhaseAveragedCurvature
  nlinarith only [h]

theorem modelPhaseAveragedCurvature_bounds
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ ≤ modelPhaseAveragedCurvature F v u ∧
      modelPhaseAveragedCurvature F v u ≤ σ+1 := by
  by_cases heq : u = modelPhaseInverseSlope F v
  · rw [heq,modelPhaseAveragedCurvature_at_inverse]
    exact modelPhaseCurvatureAt_bounds hσ hδ hF hv
  · have hp : 0 < (u-modelPhaseInverseSlope F v)^2 :=
      sq_pos_of_ne_zero (sub_ne_zero.mpr heq)
    have h := modelPhaseStationaryDeficit_bounds hσ hδ hF hv hu
    rw [modelPhaseStationaryDeficit_eq_averagedCurvature hF hv hu] at h
    constructor <;> nlinarith [h.1,h.2]

theorem modelPhaseAveragedCurvature_pos
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    0 < modelPhaseAveragedCurvature F v u :=
  (modelPhaseCurvatureLower_pos hσ).trans_le (modelPhaseAveragedCurvature_bounds hσ hδ hF hv hu).1

theorem modelPhaseMorseCoordinate_eq_smooth
    {F : ℝ → ℝ} {σ δ v u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseCoordinate F v u =
      (u-modelPhaseInverseSlope F v)*Real.sqrt (modelPhaseAveragedCurvature F v u) := by
  have he : 2*modelPhaseStationaryDeficit F v u =
      (u-modelPhaseInverseSlope F v)^2*modelPhaseAveragedCurvature F v u := by
    rw [modelPhaseStationaryDeficit_eq_averagedCurvature hF hv hu]
    ring
  rw [modelPhaseMorseCoordinate,he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]
  split_ifs with h
  · rw [abs_of_neg (sub_neg.mpr h)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))]

theorem modelPhaseMorseCoordinate_contDiffAt
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    ContDiffAt ℝ ∞ (modelPhaseMorseCoordinate F v) u := by
  have hp := modelPhaseAveragedCurvature_pos hσ hδ hF hv hu
  have hc := (modelPhaseAveragedCurvature_contDiffAt hF hv hu).sqrt hp.ne'
  have h : ContDiffAt ℝ ∞ (fun x : ℝ => (x-modelPhaseInverseSlope F v)*
      Real.sqrt (modelPhaseAveragedCurvature F v x)) u :=
    (contDiffAt_id.sub contDiffAt_const).mul hc
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
  exact modelPhaseMorseCoordinate_eq_smooth hF hv hx

theorem modelPhaseMorseCoordinate_contDiffOn
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    ContDiffOn ℝ ∞ (modelPhaseMorseCoordinate F v) (Ioo (1 : ℝ) 2) :=
  fun _ hu => (modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu).contDiffWithinAt

end TaoTrudgianYang2025
