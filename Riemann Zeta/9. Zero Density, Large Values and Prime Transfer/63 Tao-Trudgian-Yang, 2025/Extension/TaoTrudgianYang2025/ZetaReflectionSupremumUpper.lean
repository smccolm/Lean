import TaoTrudgianYang2025.ZetaReflectionCoordinates

/-! The reflected affine supremum is bounded by the original affine supremum. -/

noncomputable section
open Set
namespace TaoTrudgianYang2025

def zetaLargeValueAffineSupremum (σ τ : ℝ) : EReal :=
  ⨆ (s : ℝ) (_hs : s ∈ Icc σ 1),
    zetaLargeValueExponent s τ+((s-σ : ℝ) : EReal)

def zetaReflectedAffineSupremum (σ τ : ℝ) : EReal :=
  ⨆ (s : ℝ) (_hs : s ∈ Icc σ 1),
    zetaLargeValueExponent (zetaReflectionCoordinate s τ) (τ/(τ-1))+
      (((s-σ)/(τ-1) : ℝ) : EReal)

theorem zeta_reflected_affine_supremum_le {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    ((τ-1 : ℝ) : EReal)*zetaReflectedAffineSupremum σ τ ≤
      zetaLargeValueAffineSupremum σ τ := by
  have hκ : 0 < τ-1 := sub_pos.mpr hτ
  have hκe : (0 : EReal) ≤ ((τ-1 : ℝ) : EReal) := EReal.coe_nonneg.mpr hκ.le
  unfold zetaReflectedAffineSupremum
  rw [ereal_pos_mul_iSup _ hκ]
  apply iSup_le
  intro s
  rw [ereal_pos_mul_iSup _ hκ]
  apply iSup_le
  intro hs
  have hsHalf : 1/2 ≤ s := hσ.trans hs.1
  have href := zetaLargeValueExponent_le_reflectionMassEnvelope
    (zetaReflectionCoordinate_ge_half hsHalf hτ) (zetaReflection_time_gt_one hτ)
  have hb : ((τ-1 : ℝ) : EReal)*
      zetaLargeValueExponent (zetaReflectionCoordinate s τ) (τ/(τ-1))+
      ((s-σ : ℝ) : EReal) ≤
      ((τ-1 : ℝ) : EReal)*zetaReflectionMassEnvelope
        (zetaReflectionCoordinate s τ) (τ/(τ-1))+((s-σ : ℝ) : EReal) :=
    add_le_add (mul_le_mul_of_nonneg_left href hκe) le_rfl
  have hmain : ((τ-1 : ℝ) : EReal)*zetaReflectionMassEnvelope
      (zetaReflectionCoordinate s τ) (τ/(τ-1))+((s-σ : ℝ) : EReal) ≤
      zetaLargeValueAffineSupremum σ τ := by
    unfold zetaReflectionMassEnvelope
    rw [ereal_pos_affine_iSup _ hκ]
    apply iSup_le
    intro v
    rw [ereal_pos_affine_iSup _ hκ]
    apply iSup_le
    intro hv
    have hv' : v ∈ Icc (s/(τ-1)) (1/(τ-1)) := by
      simpa only [zetaReflection_reverse_lower hτ s,zetaReflection_time_sub_one hτ] using hv
    have hl := (div_le_iff₀ hκ).mp hv'.1
    have hu := (le_div_iff₀ hκ).mp hv'.2
    have ht : (τ-1)*v ∈ Icc σ 1 := ⟨by nlinarith [hs.1],by nlinarith⟩
    rw [zetaReflection_time_involutive hτ,zetaReflection_reverse_frequency hτ v,
      zetaReflection_time_sub_one hτ,zetaReflection_reverse_lower hτ s,
      ereal_pos_affine_comp _ hκ]
    have hc : (τ-1)*(1/(τ-1)) = 1 := by field_simp
    have ha : (τ-1)*(v-s/(τ-1))+(s-σ) = (τ-1)*v-σ := by
      field_simp
      ring
    rw [hc,ha,EReal.coe_one,one_mul]
    unfold zetaLargeValueAffineSupremum
    exact le_iSup_of_le ((τ-1)*v) (le_iSup_of_le ht le_rfl)
  have he : ((τ-1 : ℝ) : EReal)*
      (zetaLargeValueExponent (zetaReflectionCoordinate s τ) (τ/(τ-1))+
        (((s-σ)/(τ-1) : ℝ) : EReal)) =
      ((τ-1 : ℝ) : EReal)*zetaLargeValueExponent (zetaReflectionCoordinate s τ) (τ/(τ-1))+
        ((s-σ : ℝ) : EReal) := by
    rw [EReal.left_distrib_of_nonneg_of_ne_top hκe (EReal.coe_ne_top (τ-1)),
      ← EReal.coe_mul]
    have hc : (τ-1)*((s-σ)/(τ-1)) = s-σ := by field_simp
    rw [hc]
  rw [he]
  exact hb.trans hmain

end TaoTrudgianYang2025
