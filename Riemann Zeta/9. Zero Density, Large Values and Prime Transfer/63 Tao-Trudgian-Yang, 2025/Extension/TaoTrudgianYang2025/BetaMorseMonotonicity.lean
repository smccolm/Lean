import TaoTrudgianYang2025.BetaAveragedCurvature

/-!
# The actual quadratic coordinate has positive derivative

The derivative identity follows by differentiating the exact deficit,
and its sign follows from the original phase's strict negative curvature.
This supplies invertibility through the critical point.
-/

noncomputable section

open Set Expdb Filter
open scoped ContDiff Topology

namespace TaoTrudgianYang2025

theorem modelPhaseStationaryDeficit_hasDerivAt
    {F : ℝ → ℝ} {σ δ u : ℝ} {P : ℕ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (v : ℝ) (hu : u ∈ Ioo (1 : ℝ) 2) :
    HasDerivAt (modelPhaseStationaryDeficit F v) (v-deriv F u) u := by
  have hd := (approximateModelPhase_contDiffAt hF hu).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have h := ((hasDerivAt_const u (F (modelPhaseInverseSlope F v))).add
    (((hasDerivAt_id u).sub_const (modelPhaseInverseSlope F v)).const_mul v)).sub hd.hasDerivAt
  convert h using 1
  ring

theorem modelPhaseMorseCoordinate_deriv_mul
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    modelPhaseMorseCoordinate F v u * deriv (modelPhaseMorseCoordinate F v) u =
      v-deriv F u := by
  have hd := ((modelPhaseMorseCoordinate_contDiffAt hσ hδ hF hv hu).differentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)).hasDerivAt.pow 2
  have hD := (modelPhaseStationaryDeficit_hasDerivAt hF v hu).const_mul 2
  have he : (fun x => (modelPhaseMorseCoordinate F v x)^2) =ᶠ[𝓝 u]
      (fun x => 2*modelPhaseStationaryDeficit F v x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact modelPhaseMorseCoordinate_sq hσ hδ hF hv hx
  have h := hd.unique (hD.congr_of_eventuallyEq he)
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one] at h
  nlinarith only [h]

theorem modelPhaseMorseCoordinate_deriv_pos
    {F : ℝ → ℝ} {σ δ v u : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) (hu : u ∈ Ioo (1 : ℝ) 2) :
    0 < deriv (modelPhaseMorseCoordinate F v) u := by
  by_cases heq : u = modelPhaseInverseSlope F v
  · rw [heq,(modelPhaseMorseCoordinate_hasDerivAt_inverse hF hv).deriv]
    exact Real.sqrt_pos.mpr (modelPhaseCurvatureAt_pos hσ hδ hF hv)
  · have hrel := modelPhaseMorseCoordinate_deriv_mul hσ hδ hF hv hu
    have hp := Real.sqrt_pos.mpr (modelPhaseAveragedCurvature_pos hσ hδ hF hv hu)
    have hmono := approximateModelPhase_deriv_strictAntiOn hσ hδ hF
    rcases lt_or_gt_of_ne heq with hlt | hgt
    · have hw : modelPhaseMorseCoordinate F v u < 0 := by
        rw [modelPhaseMorseCoordinate_eq_smooth hF hv hu]
        exact mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hp
      have h := hmono hu (modelPhaseInverseSlope_mem hv) hlt
      rw [deriv_modelPhaseInverseSlope_apply hv] at h
      nlinarith
    · have hw : 0 < modelPhaseMorseCoordinate F v u := by
        rw [modelPhaseMorseCoordinate_eq_smooth hF hv hu]
        exact mul_pos (sub_pos.mpr hgt) hp
      have h := hmono (modelPhaseInverseSlope_mem hv) hu hgt
      rw [deriv_modelPhaseInverseSlope_apply hv] at h
      nlinarith

theorem modelPhaseMorseCoordinate_strictMonoOn
    {F : ℝ → ℝ} {σ δ v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    StrictMonoOn (modelPhaseMorseCoordinate F v) (Ioo (1 : ℝ) 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 1 2)
  · exact (modelPhaseMorseCoordinate_contDiffOn hσ hδ hF hv).continuousOn
  · intro u hu
    exact modelPhaseMorseCoordinate_deriv_pos hσ hδ hF hv (by simpa using hu)

end TaoTrudgianYang2025

