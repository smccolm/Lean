import TaoTrudgianYang2025.SargosRectangleLinearIntegral

/-! The sixth moment of the literal source consumes both linked dual blocks and its error. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

def sargosQuarticDyadicSixthMoment (N : ℕ) (Δ : ℝ) : ℝ :=
  ∫ α in Icc Δ (2*Δ), ∫ γ in Icc (-(1/(N:ℝ)^3)) (1/(N:ℝ)^3),
    ‖sargosQuarticSum N (fun _ => 1) α γ‖^6

def sargosQuarticDualSixthIntegral (M : ℕ) (N Δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ α in Icc Δ (2*Δ), ∫⁻ γ in Icc (-(1/N^3)) (1/N^3),
    ENNReal.ofReal ((sargosSlowQuarticMaximum M (fun _ => 1)
      (1/(4*α)) (-γ/(16*α^4)) (fun t => γ^2*t^6/(16*α^7)))^6)

theorem sargosQuartic_source_sixth_integral_bound :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (N : ℕ) (Δ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N:ℝ) ≤ Δ → Δ ≤ 1/2 →
      let m := sargosQuarticRoundedDualScale N Δ
      ENNReal.ofReal (sargosQuarticDyadicSixthMoment N Δ) ≤
        ENNReal.ofReal K*(ENNReal.ofReal (1/Δ^3)*
          (sargosQuarticDualSixthIntegral m N Δ+
            sargosQuarticDualSixthIntegral (2*m) N Δ)+ENNReal.ofReal (2*Δ)) := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_source_le_two_slow_blocks
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hC6 : 1 ≤ C^6 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hC 6
  refine ⟨1024*C^6,by nlinarith only [hC6],?_⟩
  intro N Δ hN hΔ hΔ₁ m
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith only [hNr]
  have hN1 : (1:ℝ) ≤ N := by linarith only [hNr]
  have hΔp := (sargosQuartic_source_scale hNr hΔ).1
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun M p => ENNReal.ofReal
    ((sargosSlowQuarticMaximum M (fun _ => 1) (1/(4*p.1)) (-p.2/(16*p.1^4))
      (fun t => p.2^2*t^6/(16*p.1^7)))^6)
  have hF (M : ℕ) : Measurable (F M) :=
    ((measurable_sargosQuarticDualMaximum M).pow_const 6).ennreal_ofReal
  rw [sargosQuarticDyadicSixthMoment,sargosQuarticNormPower_ofReal_integral]
  calc
    _ ≤ ∫⁻ α in Icc Δ (2*Δ), ∫⁻ γ in Icc (-(1/(N:ℝ)^3)) (1/(N:ℝ)^3),
        ENNReal.ofReal (1024*C^6)*(ENNReal.ofReal (1/Δ^3)*
          (F m (α,γ)+F (2*m) (α,γ))+ENNReal.ofReal ((N:ℝ)^3)) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro α hα
      dsimp only
      apply setLIntegral_mono' measurableSet_Icc
      intro γ hγ
      dsimp only
      have hγabs : |γ| ≤ 1/(N:ℝ)^3 := abs_le.mpr hγ
      have hs := hsource N Δ α γ hN hΔ hΔ₁ hα hγabs
      have hp := sargos_sixth_of_two_blocks (norm_nonneg _)
        (sargosSlowQuarticMaximum_nonneg m (fun _ => 1) _ _ _)
        (sargosSlowQuarticMaximum_nonneg (2*m) (fun _ => 1) _ _ _)
        hC0 hΔp hN1 hs
      apply (ENNReal.ofReal_le_ofReal hp).trans_eq
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 1024*C^6),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 1/Δ^3),
        ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by
      rw [sargos_rectangle_lintegral_linear (F m) (F (2*m)) (fun _ => ENNReal.ofReal ((N:ℝ)^3))
        (hF m) (hF (2*m)) measurable_const]
      rw [sargosQuartic_source_cube_lintegral hNp]
      rfl

end TaoTrudgianYang2025
