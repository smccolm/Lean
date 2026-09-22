import TaoTrudgianYang2025.BetaExpandedInverseStability

/-!
# Original derivative errors at the expanded reciprocal reference point

The reference point may lie outside [1,2]. Only the reference primitive,
which is smooth on the entire positive axis, is evaluated there. The
original phase is evaluated solely at its actual inverse point in (1,2).
All constants precede the original phase, tolerance and moving slope.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem iteratedDeriv_modelPhase_positive_compact_lipschitz
    {l r : ℝ} (hl : 0 < l) (σ : ℝ) (p : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x ∈ Icc l r, ∀ y ∈ Icc l r,
      |iteratedDeriv p (modelPhase σ) x-iteratedDeriv p (modelPhase σ) y| ≤
        C*|x-y| := by
  have hf : ∀ x ∈ Icc l r, ContDiffAt ℝ ∞ (iteratedDeriv p (modelPhase σ)) x := by
    intro x hx
    exact contDiffAt_iteratedDeriv_infty
      (Real.contDiffAt_rpow_const_of_ne (hl.trans_le hx.1).ne') p
  have hd : ContinuousOn (deriv (iteratedDeriv p (modelPhase σ))) (Icc l r) := by
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

def expandedModelPointLower (σ : ℝ) : ℝ := min 1 ((2 : ℝ)^(-σ⁻¹))

def expandedModelPointUpper (σ : ℝ) : ℝ :=
  max 2 (((2 : ℝ)^(-σ)/2)^(-σ⁻¹))

theorem expandedModelPointLower_pos (σ : ℝ) :
    0 < expandedModelPointLower σ :=
  lt_min zero_lt_one (Real.rpow_pos_of_pos (by norm_num) _)

theorem modelPhaseInverseSlope_expanded_points
    {F : ℝ → ℝ} {σ δ : ℝ} {P : ℕ} {v : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min ((2 : ℝ)^(-σ)/2) 1)
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    (hv : v ∈ modelPhaseSlopeRange F) :
    modelPhaseInverseSlope F v ∈ Icc (expandedModelPointLower σ) (expandedModelPointUpper σ) ∧
      v^(-σ⁻¹) ∈ Icc (expandedModelPointLower σ) (expandedModelPointUpper σ) := by
  have hu := modelPhaseInverseSlope_mem hv
  have hw := modelPhaseSlopeRange_positive_window hσ hδ hF hv
  have hlo : 0 < (2 : ℝ)^(-σ)/2 := by positivity
  have hvp : 0 < v := hlo.trans_le hw.1
  have hexp : -σ⁻¹ ≤ 0 := neg_nonpos.mpr (inv_nonneg.mpr hσ.le)
  have hL := Real.rpow_le_rpow_of_nonpos hvp hw.2 hexp
  have hU := Real.rpow_le_rpow_of_nonpos hlo hw.1 hexp
  exact ⟨⟨(min_le_left _ _).trans hu.1.le,hu.2.le.trans (le_max_left _ _)⟩,
    ⟨(min_le_right _ _).trans hL,hU.trans (le_max_right _ _)⟩⟩

theorem modelPhaseInverse_iteratedDeriv_expanded_reference_error
    {σ : ℝ} (hσ : 0 < σ) (p : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (F : ℝ → ℝ) (δ : ℝ) (P : ℕ),
      δ ≤ min ((2 : ℝ)^(-σ)/2) 1 →
      IsApproximateModelPhaseFunction F σ P δ → p ≤ P →
      ∀ v ∈ modelPhaseSlopeRange F,
        |iteratedDeriv (p+1) F (modelPhaseInverseSlope F v)-
          iteratedDeriv (p+1) (referenceModelPrimitive σ) (v^(-σ⁻¹))| ≤ C*δ := by
  obtain ⟨A,hA,hdisplacement⟩ := modelPhaseInverseSlope_expanded_model_error hσ
  obtain ⟨B,hB,hLip⟩ := iteratedDeriv_modelPhase_positive_compact_lipschitz
    (r := expandedModelPointUpper σ) (expandedModelPointLower_pos σ) σ p
  refine ⟨1+B*A,by nlinarith,?_⟩
  intro F δ P hδ hF hp v hv
  have hu := modelPhaseInverseSlope_mem hv
  have hw := modelPhaseInverseSlope_expanded_points hσ hδ hF hv
  have hvpos : 0 < v^(-σ⁻¹) :=
    (expandedModelPointLower_pos σ).trans_le hw.2.1
  rw [referenceModelPrimitive_iteratedDeriv σ hvpos p]
  have he := approximateModelPhase_iteratedDeriv_error hF hu p hp
  have hd := hdisplacement F δ P hδ hF v hv
  have h := hLip _ hw.1 _ hw.2
  calc
    _ ≤ |iteratedDeriv (p+1) F (modelPhaseInverseSlope F v)-
        iteratedDeriv p (modelPhase σ) (modelPhaseInverseSlope F v)|+
        |iteratedDeriv p (modelPhase σ) (modelPhaseInverseSlope F v)-
          iteratedDeriv p (modelPhase σ) (v^(-σ⁻¹))| := abs_sub_le _ _ _
    _ ≤ δ+B*(A*δ) := add_le_add he
      (h.trans (mul_le_mul_of_nonneg_left hd (zero_le_one.trans hB)))
    _ = _ := by ring

end TaoTrudgianYang2025
