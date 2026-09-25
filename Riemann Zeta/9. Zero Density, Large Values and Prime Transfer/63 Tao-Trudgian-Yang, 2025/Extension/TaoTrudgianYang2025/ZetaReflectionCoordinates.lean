import TaoTrudgianYang2025.ZetaReflectionSupremumAlgebra

/-! Exact real-coordinate algebra and the out-of-range bottom case for reflection. -/

noncomputable section
open Set
namespace TaoTrudgianYang2025

def zetaReflectionCoordinate (σ τ : ℝ) : ℝ := 1/2+(σ-1/2)/(τ-1)

theorem zetaReflectionCoordinate_eq {τ : ℝ} (hτ : 1 < τ) (σ : ℝ) :
    zetaReflectionCoordinate σ τ = (σ+τ/2-1)/(τ-1) := by
  unfold zetaReflectionCoordinate
  field_simp [(sub_pos.mpr hτ).ne']
  ring

theorem zetaReflectionCoordinate_ge_half {σ τ : ℝ} (hσ : 1/2 ≤ σ) (hτ : 1 < τ) :
    1/2 ≤ zetaReflectionCoordinate σ τ := by
  unfold zetaReflectionCoordinate
  have h := div_nonneg (sub_nonneg.mpr hσ) (sub_pos.mpr hτ).le
  linarith

theorem zetaReflection_time_gt_one {τ : ℝ} (hτ : 1 < τ) : 1 < τ/(τ-1) := by
  apply (lt_div_iff₀ (sub_pos.mpr hτ)).mpr
  linarith

theorem zetaReflection_time_sub_one {τ : ℝ} (hτ : 1 < τ) :
    τ/(τ-1)-1 = 1/(τ-1) := by
  field_simp [(sub_pos.mpr hτ).ne']
  ring

theorem zetaReflection_time_involutive {τ : ℝ} (hτ : 1 < τ) :
    (τ/(τ-1))/(τ/(τ-1)-1) = τ := by
  rw [zetaReflection_time_sub_one hτ]
  field_simp [(sub_pos.mpr hτ).ne']

theorem zetaReflection_reverse_lower {τ : ℝ} (hτ : 1 < τ) (σ : ℝ) :
    zetaReflectionCoordinate σ τ+(τ/(τ-1))/2-1 = σ/(τ-1) := by
  unfold zetaReflectionCoordinate
  field_simp [(sub_pos.mpr hτ).ne']
  ring

theorem zetaReflection_reverse_frequency {τ : ℝ} (hτ : 1 < τ) (v : ℝ) :
    v/(τ/(τ-1)-1) = (τ-1)*v := by
  rw [zetaReflection_time_sub_one hτ]
  field_simp [(sub_pos.mpr hτ).ne']

theorem zetaReflection_inverse_coordinate {τ : ℝ} (hτ : 1 < τ) (v : ℝ) :
    zetaReflectionCoordinate (v+1-τ/2) τ = v/(τ-1) := by
  rw [zetaReflectionCoordinate_eq hτ]
  congr 1
  ring

theorem zetaReflectionMassEnvelope_eq_bot_of_above_half_height {σ τ : ℝ}
    (hσ : τ/2 < σ) : zetaReflectionMassEnvelope σ τ = ⊥ := by
  apply le_antisymm _ bot_le
  unfold zetaReflectionMassEnvelope
  apply iSup_le
  intro v
  apply iSup_le
  intro hv
  have hl := hv.1
  have hu := hv.2
  exfalso
  linarith

theorem zetaLargeValueExponent_eq_bot_of_above_half_height {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hhigh : τ/2 < σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply le_antisymm _ bot_le
  exact (zetaLargeValueExponent_le_reflectionMassEnvelope hσ hτ).trans
    (le_of_eq (zetaReflectionMassEnvelope_eq_bot_of_above_half_height hhigh))

end TaoTrudgianYang2025
