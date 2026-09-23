import TaoTrudgianYang2025.SargosInitialInterval

/-! Regularity and elementary bounds for the actual initial quartic sum. -/

noncomputable section

open MeasureTheory Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_sargosInitialQuarticSum_le (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    ‖sargosInitialQuarticSum N z α γ‖ ≤ ∑ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖ := by
  unfold sargosInitialQuarticSum
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (0:ℤ) N,
        ‖z n*fordAdditiveCharacter ((n:ℝ)^2*α+(n:ℝ)^4*γ)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]

theorem norm_sargosInitialQuarticSum_le_card (N : ℕ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖ ≤ 1) (α γ : ℝ) :
    ‖sargosInitialQuarticSum N z α γ‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖ := norm_sargosInitialQuarticSum_le N z α γ
    _ ≤ ∑ _n ∈ Finset.Ioc (0:ℤ) N, (1:ℝ) := Finset.sum_le_sum hz
    _ = _ := by simp

theorem continuous_sargosInitialQuarticNormPower (N p : ℕ) (z : ℤ → ℂ) :
    Continuous (fun t : ℝ × ℝ => ‖sargosInitialQuarticSum N z t.1 t.2‖^p) := by
  unfold sargosInitialQuarticSum fordAdditiveCharacter
  fun_prop

theorem integrable_sargosInitialQuarticNormPower_rectangle (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    Integrable (fun t : ℝ × ℝ => ‖sargosInitialQuarticSum N z t.1 t.2‖^p)
      ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  refine sargos_integrable_rectangle_of_continuous_bound _
    (continuous_sargosInitialQuarticNormPower N p z)
    ((∑ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖)^p) ?_ a b c d
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg _) p)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_sargosInitialQuarticSum_le N z t.1 t.2) p

theorem integrable_sargosInitialQuarticNormPower_outer (N p : ℕ) (z : ℤ → ℂ)
    (a b c d : ℝ) :
    IntegrableOn (fun α : ℝ => ∫ γ in Icc c d,
      ‖sargosInitialQuarticSum N z α γ‖^p) (Icc a b) :=
  (integrable_sargosInitialQuarticNormPower_rectangle N p z a b c d).integral_prod_left

theorem integrable_sargosInitialQuarticNormPower_inner (N p : ℕ) (z : ℤ → ℂ)
    (α c d : ℝ) :
    IntegrableOn (fun γ : ℝ => ‖sargosInitialQuarticSum N z α γ‖^p) (Icc c d) := by
  have hc := (continuous_sargosInitialQuarticNormPower N p z).comp
    (show Continuous (fun γ : ℝ => (α,γ)) from continuous_const.prodMk continuous_id)
  exact hc.continuousOn.integrableOn_Icc

theorem sargosInitialQuartic_power_rectangle_trivial (N p : ℕ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖ ≤ 1)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (c d : ℝ) :
    (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      ‖sargosInitialQuarticSum N z α γ‖^p) ≤ lambda*(N:ℝ)^p := by
  calc
    _ ≤ ∫ _α in Icc c (c+1), ∫ _γ in Icc d (d+lambda), (N:ℝ)^p := by
      apply integral_mono
        (integrable_sargosInitialQuarticNormPower_outer N p z c (c+1) d (d+lambda))
        (integrable_const _)
      intro α
      apply integral_mono
        (integrable_sargosInitialQuarticNormPower_inner N p z α d (d+lambda))
        (integrable_const _)
      intro γ
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sargosInitialQuarticSum_le_card N z hz α γ) p
    _ = _ := by
      simp [integral_const,measureReal_def,Real.volume_Icc,hlambda]

end TaoTrudgianYang2025

