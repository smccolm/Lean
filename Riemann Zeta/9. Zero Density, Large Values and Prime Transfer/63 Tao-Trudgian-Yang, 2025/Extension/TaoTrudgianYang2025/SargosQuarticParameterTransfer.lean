import TaoTrudgianYang2025.SargosQuarticParameterChange

/-! The exact triangular change of variables and its fixed rectangular majorant. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuarticParameter_source_lintegral_change {Δ : ℝ}
    (hΔ : 0 < Δ) (H : ℝ) (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ α in Icc Δ (2*Δ), ∫⁻ γ in Icc (-H) H,
      F (sargosQuarticParameterMap (α,γ))) =
      ∫⁻ x in Icc (1/(8*Δ)) (1/(4*Δ)),
        ∫⁻ y in Icc (-16*H*x^4) (16*H*x^4),
          ENNReal.ofReal (1/(64*x^6))*F (x,y) := by
  rw [sargosQuarticParameter_horizontal_lintegral hΔ (by linarith : Δ ≤ 2*Δ)]
  rw [show 4*(2*Δ) = 8*Δ by ring]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  have hxpos : 0 < x := (by positivity : 0 < 1/(8*Δ)).trans_le hx.1
  dsimp only
  rw [sargosQuarticParameter_vertical_lintegral hxpos H,
    ← lintegral_const_mul' (ENNReal.ofReal (1/(4*x^2))) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  change ENNReal.ofReal (1/(4*x^2))*
      (ENNReal.ofReal (1/(16*x^4))*
        F (sargosQuarticParameterMap (sargosQuarticParameterMap (x,y)))) = _
  rw [sargosQuarticParameterMap_involutive (ne_of_gt hxpos),
    ← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(4*x^2))]
  rw [show (1/(4*x^2))*(1/(16*x^4)) = 1/(64*x^6) by ring]

theorem sargosQuarticParameter_vertical_extent {Δ H x : ℝ}
    (hΔ : 0 < Δ) (hH : 0 ≤ H) (hx : x ∈ Icc (1/(8*Δ)) (1/(4*Δ))) :
    16*H*x^4 ≤ H/(16*Δ^4) := by
  have hxpos : 0 < x := (by positivity : 0 < 1/(8*Δ)).trans_le hx.1
  have hp : 4*Δ*x ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*Δ)).mp hx.2
    nlinarith only [hh]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4*Δ*x) hp 4
  have hh := mul_le_mul_of_nonneg_left hpow hH
  apply (le_div_iff₀ (by positivity : 0 < 16*Δ^4)).2
  nlinarith only [hh]

theorem sargosQuarticParameter_source_lintegral_le_rectangle {Δ H : ℝ}
    (hΔ : 0 < Δ) (hH : 0 ≤ H) (F : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ α in Icc Δ (2*Δ), ∫⁻ γ in Icc (-H) H,
      F (sargosQuarticParameterMap (α,γ))) ≤
      ENNReal.ofReal (4096*Δ^6)*
        ∫⁻ x in Icc (1/(8*Δ)) (1/(4*Δ)),
          ∫⁻ y in Icc (-H/(16*Δ^4)) (H/(16*Δ^4)), F (x,y) := by
  rw [sargosQuarticParameter_source_lintegral_change hΔ,
    ← lintegral_const_mul' (ENNReal.ofReal (4096*Δ^6)) _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro x hx
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsub : Icc (-16*H*x^4) (16*H*x^4) ⊆
      Icc (-H/(16*Δ^4)) (H/(16*Δ^4)) := by
    have hh := sargosQuarticParameter_vertical_extent hΔ hH hx
    intro y hy
    constructor
    · rw [neg_div]
      linarith only [hh,hy.1]
    · exact hy.2.trans hh
  exact mul_le_mul
    (ENNReal.ofReal_le_ofReal (sargosQuarticParameter_jacobian_bound hΔ hx.1))
    (lintegral_mono_set hsub) bot_le bot_le

end TaoTrudgianYang2025
