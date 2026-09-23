import TaoTrudgianYang2025.SargosQuarticDualMoment
import TaoTrudgianYang2025.SargosQuarticSixthPower

/-! Measurability and genuine source-integral bridges for the sixth-moment assembly. -/

noncomputable section

open Set GafniTao MeasureTheory Filter
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem measurable_sargosQuarticDualMaximum (M : ℕ) :
    Measurable (fun p : ℝ × ℝ => sargosSlowQuarticMaximum M (fun _ => 1)
      (1/(4*p.1)) (-p.2/(16*p.1^4)) (fun t => p.2^2*t^6/(16*p.1^7))) := by
  unfold sargosSlowQuarticMaximum
  apply Finset.measurable_range_sup''
  intro H hH
  unfold sargosSlowQuarticPrefix fordAdditiveCharacter
  fun_prop

theorem sargosQuarticNormPower_ofReal_integral (N p : ℕ) (z : ℤ → ℂ) (a b c d : ℝ) :
    ENNReal.ofReal (∫ α in Icc a b, ∫ γ in Icc c d, ‖sargosQuarticSum N z α γ‖^p) =
      ∫⁻ α in Icc a b, ∫⁻ γ in Icc c d, ENNReal.ofReal (‖sargosQuarticSum N z α γ‖^p) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_sargosQuarticNormPower_outer N p z a b c d)
    (Eventually.of_forall (fun α => integral_nonneg (fun γ => pow_nonneg (norm_nonneg _) p)))]
  apply lintegral_congr
  intro α
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_sargosQuarticNormPower_inner N p z α c d)
    (Eventually.of_forall (fun γ => pow_nonneg (norm_nonneg _) p))

theorem sargosQuartic_source_cube_lintegral {N Δ : ℝ} (hN : 0 < N) :
    (∫⁻ _α in Icc Δ (2*Δ), ∫⁻ _γ in Icc (-(1/N^3)) (1/N^3),
      ENNReal.ofReal (N^3)) = ENNReal.ofReal (2*Δ) := by
  have hH : 0 ≤ 1/N^3+1/N^3 := by positivity
  have hwidth : 2*Δ-Δ = Δ := by ring
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
    sub_neg_eq_add,hwidth]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ N^3),
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity : 0 ≤ N^3) hH)]
  congr 1
  field_simp
  ring

end TaoTrudgianYang2025
