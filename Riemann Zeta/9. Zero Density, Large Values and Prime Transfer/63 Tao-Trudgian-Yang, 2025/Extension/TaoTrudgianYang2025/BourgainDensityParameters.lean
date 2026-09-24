import Mathlib

/-!
# Exact cutoff algebra for the improved Bourgain density bound

These certificates use Jutila with k=4. The paper's k=3 comparison is not
assumed. All real-variable inequalities are proved in the kernel.
-/

noncomputable section
namespace TaoTrudgianYang2025

def bourgainDensityCutoff (σ : ℝ) : ℝ :=
  min (9*(3*σ-2)/2) (8*(2*σ-1)/3)

def bourgainDensitySlope (σ : ℝ) : ℝ :=
  (3-3*σ)/bourgainDensityCutoff σ

theorem bourgainDensityCutoff_lower_branch {σ : ℝ} (hσ : σ ≤ 38/49) :
    bourgainDensityCutoff σ = 9*(3*σ-2)/2 := by
  unfold bourgainDensityCutoff
  exact min_eq_left (by linarith)

theorem bourgainDensityCutoff_upper_branch {σ : ℝ} (hσ : 38/49 ≤ σ) :
    bourgainDensityCutoff σ = 8*(2*σ-1)/3 := by
  unfold bourgainDensityCutoff
  exact min_eq_right (by linarith)

theorem bourgainDensityCutoff_pos {σ : ℝ} (hσ : 17/22 ≤ σ) :
    0 < bourgainDensityCutoff σ := by
  unfold bourgainDensityCutoff
  exact lt_min (by linarith) (by linarith)

theorem bourgainDensitySlope_bounds {σ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5) :
    1/3 < bourgainDensitySlope σ ∧ bourgainDensitySlope σ < 1/2 := by
  have hpos := bourgainDensityCutoff_pos hσ
  unfold bourgainDensitySlope
  rw [lt_div_iff₀ hpos, div_lt_iff₀ hpos]
  by_cases hs : σ ≤ 38/49
  · rw [bourgainDensityCutoff_lower_branch hs]
    constructor <;> linarith
  · rw [bourgainDensityCutoff_upper_branch (le_of_not_ge hs)]
    constructor <;> linarith

theorem bourgainDensitySlope_mul_cutoff {σ : ℝ} (hσ : 17/22 ≤ σ) :
    bourgainDensitySlope σ * bourgainDensityCutoff σ = 3-3*σ := by
  exact div_mul_cancel₀ _ (ne_of_gt (bourgainDensityCutoff_pos hσ))

/-- The two k=4 Jutila non-diagonal branches overlap the increasing
Bourgain affine bound on the entire closed sigma interval. -/
theorem bourgainDensity_jutila_overlap {σ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5) :
    0 ≤ bourgainDensitySlope σ*(11-7*σ)+29*σ-25 ∧
    0 ≤ bourgainDensitySlope σ*(76*σ-56)-12*σ+8 := by
  have hp := bourgainDensityCutoff_pos hσ
  have he := bourgainDensitySlope_mul_cutoff hσ
  have firstIdentity :
      bourgainDensityCutoff σ*(bourgainDensitySlope σ*(11-7*σ)+29*σ-25) =
        (3-3*σ)*(11-7*σ)+bourgainDensityCutoff σ*(29*σ-25) := by
    linear_combination (11-7*σ)*he
  have secondIdentity :
      bourgainDensityCutoff σ*(bourgainDensitySlope σ*(76*σ-56)-12*σ+8) =
        (3-3*σ)*(76*σ-56)+bourgainDensityCutoff σ*(8-12*σ) := by
    linear_combination (76*σ-56)*he
  have hfirst : 0 ≤ (3-3*σ)*(11-7*σ)+bourgainDensityCutoff σ*(29*σ-25) := by
    by_cases hs : σ ≤ 38/49
    · rw [bourgainDensityCutoff_lower_branch hs]
      nlinarith [sq_nonneg (σ-38/49)]
    · rw [bourgainDensityCutoff_upper_branch (le_of_not_ge hs)]
      nlinarith [sq_nonneg (σ-38/49)]
  have hsecond : 0 ≤ (3-3*σ)*(76*σ-56)+bourgainDensityCutoff σ*(8-12*σ) := by
    by_cases hs : σ ≤ 38/49
    · rw [bourgainDensityCutoff_lower_branch hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hσ) (sub_nonneg.mpr hs)]
    · have hl : 38/49 ≤ σ := le_of_not_ge hs
      rw [bourgainDensityCutoff_upper_branch hl]
      nlinarith [mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hσ₁)]
  constructor
  · exact nonneg_of_mul_nonneg_right (firstIdentity.symm ▸ hfirst) hp
  · exact nonneg_of_mul_nonneg_right (secondIdentity.symm ▸ hsecond) hp

/-- If the k=4 Jutila maximum does not suffice, its strict large branch
forces the remaining zero-auxiliary Bourgain affine comparison. -/
theorem bourgainDensity_affine_of_jutila_large {σ τ ρ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hfirst : 2-2*σ ≤ bourgainDensitySlope σ*τ)
    (hJ : ρ ≤ max (2-2*σ) (max (τ+(7-11*σ)/2) (τ+24-32*σ)))
    (hlarge : bourgainDensitySlope σ*τ < ρ) :
    (τ+16-20*σ)/3 ≤ bourgainDensitySlope σ*τ := by
  have hb := bourgainDensitySlope_bounds hσ hσ₁
  have ho := bourgainDensity_jutila_overlap hσ hσ₁
  rcases le_max_iff.mp hJ with hd | hJ
  · exact False.elim (not_le_of_gt hlarge (hd.trans hfirst))
  rcases le_max_iff.mp hJ with hJ | hJ
  · have hg : 0 ≤ τ+(7-11*σ)/2-bourgainDensitySlope σ*τ := by linarith
    have hprod := mul_nonneg (show 0 ≤ 3*bourgainDensitySlope σ-1 by linarith) hg
    by_contra hn
    have hprod' := mul_pos (show 0 < 1-bourgainDensitySlope σ by linarith)
      (show 0 < (τ+16-20*σ)/3-bourgainDensitySlope σ*τ by linarith)
    nlinarith
  · have hg : 0 ≤ τ+24-32*σ-bourgainDensitySlope σ*τ := by linarith
    have hprod := mul_nonneg (show 0 ≤ 3*bourgainDensitySlope σ-1 by linarith) hg
    by_contra hn
    have hprod' := mul_pos (show 0 < 1-bourgainDensitySlope σ by linarith)
      (show 0 < (τ+16-20*σ)/3-bourgainDensitySlope σ*τ by linarith)
    nlinarith

end TaoTrudgianYang2025

