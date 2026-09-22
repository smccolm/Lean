import TaoTrudgianYang2025.BetaBufferedRetainedGeometry

/-!
# Inverse stability on the full moving positive slope window

The reciprocal power is Lipschitz on a fixed positive compact interval.
This proves stability even when the actual slope lies outside the
reference interval (2^(-sigma),1). No exterior regularity of the original
phase is required or asserted.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem real_rpow_lipschitz_on_positive_compact
    {l r : ℝ} (hl : 0 < l) (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ Icc l r, ∀ y ∈ Icc l r,
      |x^p-y^p| ≤ C*|x-y| := by
  have hf : ∀ x ∈ Icc l r, ContDiffAt ℝ ∞ (fun z : ℝ => z^p) x := by
    intro x hx
    exact Real.contDiffAt_rpow_const_of_ne (hl.trans_le hx.1).ne'
  have hd : ContinuousOn (deriv (fun z : ℝ => z^p)) (Icc l r) := by
    intro x hx
    exact ((hf x hx).derivWithin (m := ∞) (by simp)).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hd
  refine ⟨max 1 B,le_max_left _ _,?_⟩
  intro x hx y hy
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hf z hz).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0))
    (fun z hz => (hB z hz).trans (le_max_right 1 B))
    (convex_Icc l r) hy hx
  simpa only [Real.norm_eq_abs] using h

theorem modelPhaseInverseSlope_expanded_model_error
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ) (P : ℕ),
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ P δ →
      ∀ v ∈ modelPhaseSlopeRange F,
        |modelPhaseInverseSlope F v-v^(-σ⁻¹)| ≤ C*δ := by
  have hbase : 0 < (2 : ℝ)^(-σ) := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨C,hC,hLip⟩ := real_rpow_lipschitz_on_positive_compact
    (r := 2) (show 0 < (2 : ℝ)^(-σ)/2 by positivity) (-σ⁻¹)
  refine ⟨C,hC,?_⟩
  intro F δ P hδ hF v hv
  have hu := modelPhaseInverseSlope_mem hv
  have hu0 : 0 < modelPhaseInverseSlope F v := zero_lt_one.trans hu.1
  have hw : (modelPhaseInverseSlope F v)^(-σ) ∈ Icc ((2 : ℝ)^(-σ)/2) 2 := by
    have hlo := Real.rpow_le_rpow_of_nonpos hu0 hu.2.le (neg_nonpos.mpr hσ.le)
    have hhi := Real.rpow_le_one_of_one_le_of_nonpos hu.1.le (neg_nonpos.mpr hσ.le)
    constructor <;> linarith
  have he := approximateModelPhase_firstDeriv_error hF hu
  rw [deriv_modelPhaseInverseSlope_apply hv,abs_sub_comm] at he
  have h := hLip _ hw v (modelPhaseSlopeRange_positive_window hσ hδ hF hv)
  rw [← Real.rpow_mul hu0.le,neg_mul_neg,mul_inv_cancel₀ hσ.ne',Real.rpow_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left he (zero_le_one.trans hC))

theorem modelPhaseLegendreDual_expanded_firstDeriv_error
    {σ : ℝ} (hσ : 0 < σ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ),
      δ ≤ min (modelPhaseCurvatureLower σ) 1 →
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ 1 δ →
      ∀ v ∈ modelPhaseSlopeRange F,
        |deriv (modelPhaseLegendreDual F) v-v^(-σ⁻¹)| ≤ C*δ := by
  obtain ⟨C,hC,hbound⟩ := modelPhaseInverseSlope_expanded_model_error hσ
  refine ⟨C,hC,?_⟩
  intro F δ hδ hpos hF v hv
  rw [deriv_modelPhaseLegendreDual hσ hδ hF hv]
  exact hbound F δ 1 hpos hF v hv

end TaoTrudgianYang2025
