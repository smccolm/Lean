import TaoTrudgianYang2025.BourgainDensityLargeValues
import TaoTrudgianYang2025.ZeroDensityTransferCorollaries
import TaoTrudgianYang2025.ZetaTwelfthMoment

/-!
# The exact improved Bourgain density output

The source interval and both rational branches are unchanged. The proof
uses the genuine Jutila k=4 bound in place of the insufficient k=3
intermediate comparison in the printed argument.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem bourgainDensity_cutoff_twelfth {σ : ℝ} (hσ : σ ≤ 4/5) :
    bourgainDensityCutoff σ ≤ 3*(4*σ-1)/4 := by
  have h := min_le_right (9*(3*σ-2)/2) (8*(2*σ-1)/3)
  change bourgainDensityCutoff σ ≤ _ at h
  linarith

theorem bourgainDensity_twelfth_comparison {σ τ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτ : τ ≤ 4*bourgainDensityCutoff σ/3) :
    2*τ-12*(σ-1/2) ≤ bourgainDensitySlope σ*τ := by
  have hb := bourgainDensitySlope_bounds hσ hσ₁
  have he := bourgainDensitySlope_mul_cutoff hσ
  have hc := bourgainDensity_cutoff_twelfth hσ₁
  nlinarith [mul_nonneg (show 0 ≤ 2-bourgainDensitySlope σ by linarith)
    (sub_nonneg.mpr hτ)]

theorem bourgainDensity_zetaLargeValueBound {σ τ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5)
    (hτlo : 2 ≤ τ) (hτhi : τ ≤ 4*bourgainDensityCutoff σ/3) :
    IsZetaLargeValueBound σ τ (bourgainDensitySlope σ*τ) :=
  isZetaLargeValueBound_of_exponent_le
    ((zetaLargeValueExponent_le_of_bound
      (zetaTwelfth_largeValueBound (by linarith : 1/2 ≤ σ) hτlo)).trans
        (EReal.coe_le_coe_iff.mpr (bourgainDensity_twelfth_comparison hσ hσ₁ hτhi)))

theorem bourgainDensity_three_div_cutoff {σ : ℝ}
    (hσ : 17/22 ≤ σ) :
    3/bourgainDensityCutoff σ =
      max (2/(9*σ-6)) (9/(8*(2*σ-1))) := by
  have h1 : 0 < 9*σ-6 := by linarith
  have h2 : 0 < 8*(2*σ-1) := by linarith
  have h3 : 3*σ-2 ≠ 0 := by linarith
  have h4 : 2*σ-1 ≠ 0 := by linarith
  by_cases hs : σ ≤ 38/49
  · rw [bourgainDensityCutoff_lower_branch hs,
      max_eq_left ((div_le_div_iff₀ h2 h1).mpr (by linarith))]
    field_simp [h3,h4]
    ring
  · rw [bourgainDensityCutoff_upper_branch (le_of_not_ge hs),
      max_eq_right ((div_le_div_iff₀ h1 h2).mpr (by linarith))]
    field_simp [h3,h4]
    ring

/-- The improved Bourgain output in the paper's full uniform, shifted,
multiplicity-weighted zero-count convention. No analytic input is assumed. -/
theorem bourgain_improved_isZeroDensityBound {σ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5) :
    IsZeroDensityBound σ (max (2/(9*σ-6)) (9/(8*(2*σ-1)))) := by
  have h := isZeroDensityBound_of_two_thirds_largeValue_ranges
    σ (bourgainDensitySlope σ) (bourgainDensityCutoff σ)
    (by linarith) (by linarith)
    (le_of_lt ((by norm_num : (0:ℝ) < 1/3).trans
      (bourgainDensitySlope_bounds hσ hσ₁).1))
    (bourgainDensityCutoff_pos hσ)
    (fun τ ht => bourgainDensity_zetaLargeValueBound hσ hσ₁ ht.1 ht.2.le)
    (fun τ ht => bourgainDensity_largeValueBound hσ hσ₁ ht.1 ht.2)
  have he : bourgainDensitySlope σ/(1-σ) = 3/bourgainDensityCutoff σ := by
    have hg : 1-σ ≠ 0 := by linarith
    unfold bourgainDensitySlope
    field_simp
  rw [he, bourgainDensity_three_div_cutoff hσ] at h
  exact h

/-- Exact source theorem bourgain-density-improved. -/
theorem zeroDensityExponent_le_bourgain_improved {σ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 4/5) :
    zeroDensityExponent σ ≤
      ((max (2/(9*σ-6)) (9/(8*(2*σ-1))) : ℝ) : EReal) :=
  zeroDensityExponent_le_of_bound (bourgain_improved_isZeroDensityBound hσ hσ₁)

theorem zeroDensityExponent_le_bourgain_improved_lower {σ : ℝ}
    (hσ : 17/22 ≤ σ) (hσ₁ : σ ≤ 38/49) :
    zeroDensityExponent σ ≤ ((2/(9*σ-6) : ℝ) : EReal) := by
  have h := zeroDensityExponent_le_bourgain_improved hσ (by linarith : σ ≤ 4/5)
  have h1 : 0 < 9*σ-6 := by linarith
  have h2 : 0 < 8*(2*σ-1) := by linarith
  rwa [max_eq_left ((div_le_div_iff₀ h2 h1).mpr (by linarith))] at h

theorem zeroDensityExponent_le_bourgain_improved_upper {σ : ℝ}
    (hσ : 38/49 ≤ σ) (hσ₁ : σ ≤ 4/5) :
    zeroDensityExponent σ ≤ ((9/(8*(2*σ-1)) : ℝ) : EReal) := by
  have h := zeroDensityExponent_le_bourgain_improved (by linarith : 17/22 ≤ σ) hσ₁
  have h1 : 0 < 9*σ-6 := by linarith
  have h2 : 0 < 8*(2*σ-1) := by linarith
  rwa [max_eq_right ((div_le_div_iff₀ h1 h2).mpr (by linarith))] at h

end TaoTrudgianYang2025
