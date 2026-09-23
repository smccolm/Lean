import TaoTrudgianYang2025.SargosQuarticPrefixBounds

/-! Actual rectangle integrability for the fourth moments and the prefix maximum. -/

noncomputable section

open MeasureTheory Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_integrable_rectangle_of_continuous_bound (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (M : ℝ) (hM : ∀ p, ‖f p‖ ≤ M) (a b c d : ℝ) :
    Integrable f ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  have hc : Integrable (fun _p : ℝ × ℝ => M)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := integrable_const _
  exact hc.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hM)

theorem continuous_sargosQuarticNormFour (N : ℕ) (z : ℤ → ℂ) :
    Continuous (fun p : ℝ × ℝ => ‖sargosQuarticSum N z p.1 p.2‖^4) := by
  unfold sargosQuarticSum sargosPlanarSum fordAdditiveCharacter
  fun_prop

theorem integrable_sargosQuarticNormFour_rectangle (N : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    Integrable (fun p : ℝ × ℝ => ‖sargosQuarticSum N z p.1 p.2‖^4)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    (continuous_sargosQuarticNormFour N z) ((∑ n ∈ sargosSourceInterval N, ‖z n‖)^4) ?_ a b c d
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ‖sargosQuarticSum N z p.1 p.2‖^4)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_sargosPlanarSum_le_sum_norm (sargosSourceInterval N) z
      (fun n => (n : ℝ)^2) (fun n => (n : ℝ)^4) p.1 p.2) 4

theorem integrable_sargosQuarticNormFour_outer (N : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    IntegrableOn (fun α : ℝ => ∫ γ in Icc c d, ‖sargosQuarticSum N z α γ‖^4) (Icc a b) :=
  (integrable_sargosQuarticNormFour_rectangle N z a b c d).integral_prod_left

theorem integrable_sargosQuarticNormFour_inner (N : ℕ) (z : ℤ → ℂ)
    (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => ‖sargosQuarticSum N z α γ‖^4) (Icc c d) := by
  have hc : Continuous (fun γ : ℝ => ‖sargosQuarticSum N z α γ‖^4) := by
    unfold sargosQuarticSum sargosPlanarSum fordAdditiveCharacter
    fun_prop
  exact hc.continuousOn.integrableOn_Icc

theorem integrable_sargosQuarticPrefixMaximum_rectangle (N : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    Integrable (fun p : ℝ × ℝ => (sargosQuarticPrefixMaximum N z p.1 p.2)^4)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    ((continuous_sargosQuarticPrefixMaximum N z).pow 4)
    ((∑ n ∈ sargosSourceInterval N, ‖z n‖)^4) ?_ a b c d
  intro p
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity :
    0 ≤ (sargosQuarticPrefixMaximum N z p.1 p.2)^4)]
  exact pow_le_pow_left₀ (sargosQuarticPrefixMaximum_nonneg N z p.1 p.2)
    (sargosQuarticPrefixMaximum_le_sum_norm N z p.1 p.2) 4

theorem integrable_sargosQuarticPrefixMaximum_outer (N : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    IntegrableOn (fun α : ℝ => ∫ γ in Icc c d, (sargosQuarticPrefixMaximum N z α γ)^4)
      (Icc a b) :=
  (integrable_sargosQuarticPrefixMaximum_rectangle N z a b c d).integral_prod_left

theorem integrable_sargosQuarticPrefixMaximum_inner (N : ℕ) (z : ℤ → ℂ)
    (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => (sargosQuarticPrefixMaximum N z α γ)^4) (Icc c d) := by
  have hc : Continuous (fun γ : ℝ => (sargosQuarticPrefixMaximum N z α γ)^4) := by
    exact (((continuous_sargosQuarticPrefixMaximum N z).comp
      (continuous_const.prodMk continuous_id))).pow 4
  exact hc.continuousOn.integrableOn_Icc

end TaoTrudgianYang2025
