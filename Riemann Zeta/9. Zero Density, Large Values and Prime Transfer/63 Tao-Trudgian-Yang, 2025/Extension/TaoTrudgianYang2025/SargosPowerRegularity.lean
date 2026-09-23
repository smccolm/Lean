import TaoTrudgianYang2025.SargosQuarticMomentRegularity

/-! Arbitrary natural powers of the fixed sum and actual prefix maximum are integrable. -/

noncomputable section

open MeasureTheory Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem continuous_sargosQuarticNormPower (N p : ℕ) (z : ℤ → ℂ) :
    Continuous (fun t : ℝ × ℝ => ‖sargosQuarticSum N z t.1 t.2‖^p) := by
  unfold sargosQuarticSum sargosPlanarSum fordAdditiveCharacter
  fun_prop

theorem integrable_sargosQuarticNormPower_rectangle (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    Integrable (fun t : ℝ × ℝ => ‖sargosQuarticSum N z t.1 t.2‖^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    (continuous_sargosQuarticNormPower N p z) ((∑ n ∈ sargosSourceInterval N, ‖z n‖)^p)
    ?_ a b c d
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) p)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_sargosPlanarSum_le_sum_norm (sargosSourceInterval N) z
      (fun n => (n : ℝ)^2) (fun n => (n : ℝ)^4) t.1 t.2) p

theorem integrable_sargosQuarticNormPower_outer (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    IntegrableOn (fun α : ℝ => ∫ γ in Icc c d, ‖sargosQuarticSum N z α γ‖^p) (Icc a b) :=
  (integrable_sargosQuarticNormPower_rectangle N p z a b c d).integral_prod_left

theorem integrable_sargosQuarticNormPower_inner (N p : ℕ) (z : ℤ → ℂ)
    (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => ‖sargosQuarticSum N z α γ‖^p) (Icc c d) := by
  have hc := (continuous_sargosQuarticNormPower N p z).comp
    (show Continuous (fun γ : ℝ => (α,γ)) from continuous_const.prodMk continuous_id)
  exact hc.continuousOn.integrableOn_Icc

theorem integrable_sargosQuarticMaximumPower_rectangle (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    Integrable (fun t : ℝ × ℝ => (sargosQuarticPrefixMaximum N z t.1 t.2)^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    ((continuous_sargosQuarticPrefixMaximum N z).pow p)
    ((∑ n ∈ sargosSourceInterval N, ‖z n‖)^p) ?_ a b c d
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg
    (pow_nonneg (sargosQuarticPrefixMaximum_nonneg N z t.1 t.2) p)]
  exact pow_le_pow_left₀ (sargosQuarticPrefixMaximum_nonneg N z t.1 t.2)
    (sargosQuarticPrefixMaximum_le_sum_norm N z t.1 t.2) p

theorem integrable_sargosQuarticMaximumPower_outer (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    IntegrableOn
      (fun α : ℝ => ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^p) (Icc a b) :=
  (integrable_sargosQuarticMaximumPower_rectangle N p z a b c d).integral_prod_left

theorem integrable_sargosQuarticMaximumPower_inner (N p : ℕ) (z : ℤ → ℂ)
    (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => (sargosQuarticPrefixMaximum N z α γ)^p) (Icc c d) := by
  have hc := (continuous_sargosQuarticPrefixMaximum N z).comp
    (show Continuous (fun γ : ℝ => (α,γ)) from continuous_const.prodMk continuous_id)
  exact (hc.pow p).continuousOn.integrableOn_Icc

end TaoTrudgianYang2025

