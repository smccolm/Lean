import TaoTrudgianYang2025.SargosQuarticSecondDerivative

/-! All finite unweighted moments are genuine integrable rectangle functions. -/

noncomputable section

open MeasureTheory GafniTao Set RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticPrefixMaximum_unweighted_le (N : ℕ) (α γ : ℝ) :
    sargosQuarticPrefixMaximum N (fun _ => 1) α γ ≤ (N : ℝ) := by
  obtain ⟨H,hH,he⟩ := sargosQuarticPrefixMaximum_attained N (fun _ => 1) α γ
  rw [he,sargosQuarticPrefix_eq_radian_sum]
  calc
    _ ≤ (H : ℝ) := by
      simpa using norm_phase_sum_finset_le_card (Finset.range H)
        (fun j => sargosQuarticRadianSample N α γ j)
    _ ≤ _ := by exact_mod_cast hH

theorem continuous_sargosQuarticUnweightedPower (N p : ℕ) :
    Continuous (fun t : ℝ × ℝ => (sargosQuarticPrefixMaximum N (fun _ => 1) t.1 t.2)^p) :=
  (continuous_sargosQuarticPrefixMaximum N (fun _ => 1)).pow p

theorem integrable_sargosQuarticUnweightedPower_rectangle (N p : ℕ)
    (a b c d : ℝ) :
    Integrable (fun t : ℝ × ℝ => (sargosQuarticPrefixMaximum N (fun _ => 1) t.1 t.2)^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    (continuous_sargosQuarticUnweightedPower N p) ((N : ℝ)^p) ?_ a b c d
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg
    (pow_nonneg (sargosQuarticPrefixMaximum_nonneg N (fun _ => 1) t.1 t.2) p)]
  exact pow_le_pow_left₀ (sargosQuarticPrefixMaximum_nonneg N (fun _ => 1) t.1 t.2)
    (sargosQuarticPrefixMaximum_unweighted_le N t.1 t.2) p

theorem integrable_sargosQuarticUnweightedPower_outer (N p : ℕ)
    (a b c d : ℝ) :
    IntegrableOn
      (fun α : ℝ => ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^p)
      (Icc a b) :=
  (integrable_sargosQuarticUnweightedPower_rectangle N p a b c d).integral_prod_left

theorem integrable_sargosQuarticUnweightedPower_inner (N p : ℕ) (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^p)
      (Icc c d) := by
  have hc := (continuous_sargosQuarticPrefixMaximum N (fun _ => 1)).comp
    (show Continuous (fun γ : ℝ => (α,γ)) from continuous_const.prodMk continuous_id)
  exact (hc.pow p).continuousOn.integrableOn_Icc

end TaoTrudgianYang2025
