import TaoTrudgianYang2025.BetaCanonicalTaylorLegendre

/-!
# A physical buffer and exact coverage of every retained stationary integer

The extension width is chosen from the actual original curvature scale.
Its admissibility and coverage are derived from the original source
endpoints and the already constructed retained set.
-/

noncomputable section

open Set Expdb

namespace TaoTrudgianYang2025

def modelPhaseTaylorWidth (σ η : ℝ) : ℝ :=
  min (modelPhaseCurvatureLower σ) 1*η/4

theorem modelPhaseTaylorWidth_pos {σ η : ℝ} (hσ : 0 < σ) (hη : 0 < η) :
    0 < modelPhaseTaylorWidth σ η := by
  exact div_pos (mul_pos (lt_min (modelPhaseCurvatureLower_pos hσ) zero_lt_one) hη)
    (by norm_num)

theorem modelPhaseTaylorWidth_le_one {σ η : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1) :
    modelPhaseTaylorWidth σ η ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (min_le_right (modelPhaseCurvatureLower σ) 1) hη
  dsimp [modelPhaseTaylorWidth]
  linarith

theorem modelPhaseTaylorWidth_admissible
    {F : ℝ → ℝ} {σ δ η : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hη : 0 < η) (hη₁ : η < 1) :
    0 < modelPhaseTaylorWidth σ η ∧ modelPhaseTaylorWidth σ η ≤ 1 ∧
      modelPhaseClosedSlope F 2+4*modelPhaseTaylorWidth σ η < modelPhaseClosedSlope F 1 := by
  have hc := modelPhaseCurvatureLower_pos hσ
  have hw := modelPhaseClosedSlope_endpoint_width hσ hδ hF
  have hm := mul_le_mul_of_nonneg_right (min_le_left (modelPhaseCurvatureLower σ) 1) hη.le
  have hlt : modelPhaseCurvatureLower σ*η < modelPhaseCurvatureLower σ := by nlinarith
  refine ⟨modelPhaseTaylorWidth_pos hσ hη,modelPhaseTaylorWidth_le_one hη.le hη₁.le,?_⟩
  dsimp [modelPhaseTaylorWidth]
  linarith

theorem modelPhaseSharpStationarySet_taylor_plateau
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b : ℕ} {q : ℤ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hq : q ∈ modelPhaseSharpStationarySet F T N a b) :
    (q : ℝ)*N/T ∈ Icc
      (modelPhaseClosedSlope F 2+2*modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹))
      (modelPhaseClosedSlope F 1-2*modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹)) := by
  have hg := modelPhaseSharpStationarySet_critical_geometry hσ hδ hF hT hN ha hb hq
  have hu := modelPhaseInverseSlope_mem hg.1
  have hη : 0 < (Real.sqrt T)⁻¹ := by positivity
  have hc := modelPhaseCurvatureLower_pos hσ
  have hd : 0 ≤ N/(T*(σ+1)) := by positivity
  have ha' : 1 ≤ (a : ℝ)/N := (one_le_div hN).mpr ha
  have hb' : (b : ℝ)/N ≤ 2 := (div_le_iff₀ hN).mpr hb
  have huL : 1+2*(Real.sqrt T)⁻¹ ≤ modelPhaseInverseSlope F ((q : ℝ)*N/T) := by
    linarith [hg.2.1]
  have huR : modelPhaseInverseSlope F ((q : ℝ)*N/T) ≤ 2-2*(Real.sqrt T)⁻¹ := by
    linarith [hg.2.2]
  have hdropL := modelPhaseClosedSlope_drop hσ hδ hF
    ⟨hu.1.le,hu.2.le⟩ (by norm_num : (2 : ℝ) ∈ Icc 1 2) hu.2.le
  have hdropR := modelPhaseClosedSlope_drop hσ hδ hF
    (by norm_num : (1 : ℝ) ∈ Icc 1 2) ⟨hu.1.le,hu.2.le⟩ hu.1.le
  rw [modelPhaseClosedSlope_eq_deriv hu,deriv_modelPhaseInverseSlope_apply hg.1] at hdropL hdropR
  have hm := mul_le_mul_of_nonneg_right (min_le_left (modelPhaseCurvatureLower σ) 1) hη.le
  unfold modelPhaseTaylorWidth
  constructor <;> nlinarith

theorem modelPhaseTaylorWidth_source_admissible
    {F : ℝ → ℝ} {σ δ T N : ℝ} {a b : ℕ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (ha : N ≤ (a : ℝ)) (hb : (b : ℝ) ≤ 2*N)
    (hlong : (a : ℝ)/N+4*(Real.sqrt T)⁻¹ < (b : ℝ)/N) :
    0 < modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹) ∧
      modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹) ≤ 1 ∧
      modelPhaseClosedSlope F 2+4*modelPhaseTaylorWidth σ ((Real.sqrt T)⁻¹) <
        modelPhaseClosedSlope F 1 := by
  have hη : 0 < (Real.sqrt T)⁻¹ := by positivity
  have ha' : 1 ≤ (a : ℝ)/N := (one_le_div hN).mpr ha
  have hb' : (b : ℝ)/N ≤ 2 := (div_le_iff₀ hN).mpr hb
  have hη₁ : (Real.sqrt T)⁻¹ < 1 := by linarith
  exact modelPhaseTaylorWidth_admissible hσ hδ hF hη hη₁

end TaoTrudgianYang2025
