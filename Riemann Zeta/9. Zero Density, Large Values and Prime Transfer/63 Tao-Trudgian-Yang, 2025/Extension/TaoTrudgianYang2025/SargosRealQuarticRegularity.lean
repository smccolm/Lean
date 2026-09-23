import TaoTrudgianYang2025.SargosRealQuarticPrefix

/-! Continuity and genuine rectangle integrability for real-scale prefix maxima. -/

noncomputable section

open MeasureTheory Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem continuous_sargosRealQuarticMaximum (M : ℝ) (z : ℤ → ℂ) :
    Continuous (fun t : ℝ × ℝ => sargosRealQuarticMaximum M z t.1 t.2) := by
  unfold sargosRealQuarticMaximum
  apply Continuous.finset_sup'_apply
  intro H hH
  unfold sargosRealQuarticPrefix fordAdditiveCharacter
  fun_prop

theorem integrable_sargosRealQuarticPower_rectangle {M : ℝ} (hM : 0 ≤ M)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1)
    (p : ℕ) (a b c d : ℝ) :
    Integrable (fun t : ℝ × ℝ => (sargosRealQuarticMaximum M z t.1 t.2)^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    ((continuous_sargosRealQuarticMaximum M z).pow p)
    (((∑ n ∈ sargosSourceInterval ⌊M⌋₊, ‖z n‖)+1)^p) ?_ a b c d
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg
    (sargosRealQuarticMaximum_nonneg M z t.1 t.2) p)]
  apply pow_le_pow_left₀ (sargosRealQuarticMaximum_nonneg M z t.1 t.2)
  exact (sargosRealQuarticMaximum_le_natural hM z hz t.1 t.2).trans
    (add_le_add (sargosQuarticPrefixMaximum_le_sum_norm ⌊M⌋₊ z t.1 t.2) le_rfl)

theorem integrable_sargosRealQuarticPower_outer {M : ℝ} (hM : 0 ≤ M)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1)
    (p : ℕ) (a b c d : ℝ) :
    IntegrableOn
      (fun α : ℝ => ∫ γ in Icc c d, (sargosRealQuarticMaximum M z α γ)^p) (Icc a b) :=
  (integrable_sargosRealQuarticPower_rectangle hM z hz p a b c d).integral_prod_left

theorem integrable_sargosRealQuarticPower_inner (M : ℝ) (z : ℤ → ℂ)
    (p : ℕ) (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => (sargosRealQuarticMaximum M z α γ)^p) (Icc c d) := by
  have hc := (continuous_sargosRealQuarticMaximum M z).comp
    (show Continuous (fun γ : ℝ => (α,γ)) from continuous_const.prodMk continuous_id)
  exact (hc.pow p).continuousOn.integrableOn_Icc

end TaoTrudgianYang2025
