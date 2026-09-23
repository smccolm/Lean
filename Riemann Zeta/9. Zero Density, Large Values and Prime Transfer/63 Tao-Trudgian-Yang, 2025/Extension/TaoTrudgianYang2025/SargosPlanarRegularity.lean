import TaoTrudgianYang2025.SargosPlanarNearBound
import Mathlib.MeasureTheory.Integral.Prod

/-! Actual finite-sum bounds and integrability on real rectangles. -/

noncomputable section

open MeasureTheory Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_sargosPlanarSum_le_sum_norm {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (α γ : ℝ) :
    ‖sargosPlanarSum S z u v α γ‖ ≤ ∑ i ∈ S, ‖z i‖ := by
  unfold sargosPlanarSum
  calc
    _ ≤ ∑ i ∈ S, ‖z i*fordAdditiveCharacter (u i*α+v i*γ)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul,sargos_character_norm,mul_one]

theorem continuous_sargosPlanarNormSq {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) :
    Continuous (fun p : ℝ × ℝ => ‖sargosPlanarSum S z u v p.1 p.2‖^2) := by
  unfold sargosPlanarSum fordAdditiveCharacter
  fun_prop

theorem integrable_sargosPlanarNormSq_rectangle {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (c δ d lambda : ℝ) :
    Integrable (fun p : ℝ × ℝ => ‖sargosPlanarSum S z u v p.1 p.2‖^2)
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda)))) := by
  have hM : 0 ≤ ∑ i ∈ S, ‖z i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hc : Integrable (fun _p : ℝ × ℝ => (∑ i ∈ S, ‖z i‖)^2)
      ((volume.restrict (Icc c (c+δ))).prod (volume.restrict (Icc d (d+lambda)))) :=
    integrable_const _
  apply hc.mono' (continuous_sargosPlanarNormSq S z u v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (norm_sargosPlanarSum_le_sum_norm S z u v p.1 p.2))

theorem integrable_sargosPlanarNormSq_window_outer {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (c δ d lambda : ℝ) :
    IntegrableOn (fun α : ℝ => ∫ γ in Icc d (d+lambda),
      ‖sargosPlanarSum S z u v α γ‖^2) (Icc c (c+δ)) :=
  (integrable_sargosPlanarNormSq_rectangle S z u v c δ d lambda).integral_prod_left

theorem integrable_sargosPlanarNormSq_window_inner {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (u v : ι → ℝ) (d lambda α : ℝ) :
    IntegrableOn (fun γ : ℝ => ‖sargosPlanarSum S z u v α γ‖^2) (Icc d (d+lambda)) := by
  have hc : Continuous (fun γ : ℝ => ‖sargosPlanarSum S z u v α γ‖^2) := by
    unfold sargosPlanarSum fordAdditiveCharacter
    fun_prop
  exact hc.continuousOn.integrableOn_Icc

end TaoTrudgianYang2025
