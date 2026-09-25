import TaoTrudgianYang2025.ZetaReflectionSupremumUpper

/-! The original affine supremum is bounded by the reflected affine supremum. -/

noncomputable section
open Set
namespace TaoTrudgianYang2025

theorem zeta_affine_supremum_le_reflected {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    zetaLargeValueAffineSupremum σ τ ≤
      ((τ-1 : ℝ) : EReal)*zetaReflectedAffineSupremum σ τ := by
  have hκ : 0 < τ-1 := sub_pos.mpr hτ
  have hκe : (0 : EReal) ≤ ((τ-1 : ℝ) : EReal) := EReal.coe_nonneg.mpr hκ.le
  unfold zetaLargeValueAffineSupremum
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  have hsHalf : 1/2 ≤ s := hσ.trans hs.1
  have href := zetaLargeValueExponent_le_reflectionMassEnvelope hsHalf hτ
  have hb : zetaLargeValueExponent s τ+((s-σ : ℝ) : EReal) ≤
      zetaReflectionMassEnvelope s τ+((s-σ : ℝ) : EReal) :=
    add_le_add href le_rfl
  apply hb.trans
  unfold zetaReflectionMassEnvelope
  rw [ereal_iSup_add_real]
  apply iSup_le
  intro v
  rw [ereal_iSup_add_real]
  apply iSup_le
  intro hv
  let t := v+1-τ/2
  have hst : s ≤ t := by dsimp [t]; linarith [hv.1]
  have htHalf : 1/2 ≤ t := hsHalf.trans hst
  have hcoord : zetaReflectionCoordinate t τ = v/(τ-1) :=
    zetaReflection_inverse_coordinate hτ v
  by_cases ht1 : t ≤ 1
  · have ht : t ∈ Icc σ 1 := ⟨hs.1.trans hst,ht1⟩
    have hterm : zetaLargeValueExponent (zetaReflectionCoordinate t τ) (τ/(τ-1))+
        (((t-σ)/(τ-1) : ℝ) : EReal) ≤ zetaReflectedAffineSupremum σ τ := by
      unfold zetaReflectedAffineSupremum
      exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
    have hm := mul_le_mul_of_nonneg_left hterm hκe
    rw [EReal.left_distrib_of_nonneg_of_ne_top hκe (EReal.coe_ne_top (τ-1)),
      ← EReal.coe_mul] at hm
    have hc : (τ-1)*((t-σ)/(τ-1)) = t-σ := by field_simp
    rw [hc,hcoord] at hm
    rw [add_assoc,← EReal.coe_add]
    have ha : v-(s+τ/2-1)+(s-σ) = t-σ := by dsimp [t]; ring
    rw [ha]
    exact hm
  · have hvhigh : τ/2 < v := by dsimp [t] at ht1; linarith
    have hhigh : (τ/(τ-1))/2 < v/(τ-1) := by
      calc
        _ = (τ/2)/(τ-1) := by ring
        _ < _ := div_lt_div_of_pos_right hvhigh hκ
    have hhalf : 1/2 ≤ v/(τ-1) := by
      rw [← hcoord]
      exact zetaReflectionCoordinate_ge_half htHalf hτ
    have hbot := zetaLargeValueExponent_eq_bot_of_above_half_height
      hhalf (zetaReflection_time_gt_one hτ) hhigh
    rw [hbot,EReal.coe_mul_bot_of_pos hκ,EReal.bot_add,EReal.bot_add]
    exact bot_le

theorem zeta_reflection_affine_supremum_identity {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    zetaReflectedAffineSupremum σ τ =
      ((1/(τ-1) : ℝ) : EReal)*zetaLargeValueAffineSupremum σ τ := by
  have hκ : 0 < τ-1 := sub_pos.mpr hτ
  have he : ((τ-1 : ℝ) : EReal)*zetaReflectedAffineSupremum σ τ =
      zetaLargeValueAffineSupremum σ τ :=
    le_antisymm (zeta_reflected_affine_supremum_le hσ hτ)
      (zeta_affine_supremum_le_reflected hσ hτ)
  rw [← he,← mul_assoc,← EReal.coe_mul]
  have hc : (1/(τ-1))*(τ-1) = 1 := by field_simp
  rw [hc,EReal.coe_one,one_mul]

/-- The printed reflection identity, at its explicit affine supremum rather
than the informal pointwise heuristic. The same identity also holds for
sigma above one, when the indexing interval is empty. -/
theorem zetaLargeValueExponent_reflection_supremum {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    (⨆ (s : ℝ) (_hs : s ∈ Icc σ 1),
      zetaLargeValueExponent (1/2+(s-1/2)/(τ-1)) (τ/(τ-1))+
        (((s-σ)/(τ-1) : ℝ) : EReal)) =
      ((1/(τ-1) : ℝ) : EReal)*
        (⨆ (s : ℝ) (_hs : s ∈ Icc σ 1),
          zetaLargeValueExponent s τ+((s-σ : ℝ) : EReal)) :=
  zeta_reflection_affine_supremum_identity hσ hτ

end TaoTrudgianYang2025
