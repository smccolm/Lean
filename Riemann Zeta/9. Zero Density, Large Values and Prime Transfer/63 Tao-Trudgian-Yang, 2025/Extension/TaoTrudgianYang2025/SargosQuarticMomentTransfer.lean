import TaoTrudgianYang2025.SargosQuarticSexticRectangle

/-! Source-linked moment transfer and the actual measurable sextic maxima. -/

noncomputable section

open Set GafniTao MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem measurable_sargosQuarticSexticMaximum (M : ℕ) :
    Measurable (fun p : ℝ × ℝ => sargosSlowQuarticMaximum M (fun _ => 1)
      p.1 p.2 (fun t => 4*p.2^2/p.1*t^6)) := by
  unfold sargosSlowQuarticMaximum
  apply Finset.measurable_range_sup''
  intro H hH
  unfold sargosSlowQuarticPrefix fordAdditiveCharacter
  fun_prop

theorem sargosQuarticSextic_rectangle_lintegral {M : ℕ}
    (hM : 2 ≤ M) {Δ c d : ℝ} (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2)
    (hc : 1/(8*Δ) ≤ c) (hd : |d| ≤ 5/(Δ*(M:ℝ)^3)) :
    (∫⁻ x in Icc c (c+1), ∫⁻ y in Icc d (d+2/(M:ℝ)^3),
      ENNReal.ofReal ((sargosSlowQuarticMaximum M (fun _ => 1) x y
        (fun t => 4*y^2/x*t^6))^6)) ≤
      ENNReal.ofReal (384*sargosWindowConstant 3 1916928*
        (Real.log M)^6*sargosSixthBaseMoment M) := by
  have hm := ((measurable_sargosQuarticSexticMaximum M).pow_const 6).ennreal_ofReal
  have hh := sargosQuarticSextic_rectangle_upper_moment hM hΔ hΔ₁ hc hd
  rw [sargosUpperIntegral_eq_lintegral hm.aemeasurable,lintegral_prod _ hm.aemeasurable] at hh
  exact hh

theorem sargosQuarticDual_sixth_parameter_transfer (M : ℕ) {N Δ : ℝ}
    (hN : 0 < N) (hΔ : 0 < Δ) :
    (∫⁻ α in Icc Δ (2*Δ), ∫⁻ γ in Icc (-(1/N^3)) (1/N^3),
      ENNReal.ofReal ((sargosSlowQuarticMaximum M (fun _ => 1)
        (1/(4*α)) (-γ/(16*α^4)) (fun t => γ^2*t^6/(16*α^7)))^6)) ≤
      ENNReal.ofReal (4096*Δ^6)*
        ∫⁻ x in Icc (1/(8*Δ)) (1/(4*Δ)),
          ∫⁻ y in Icc (-(1/N^3)/(16*Δ^4)) ((1/N^3)/(16*Δ^4)),
            ENNReal.ofReal ((sargosSlowQuarticMaximum M (fun _ => 1)
              x y (fun t => 4*y^2/x*t^6))^6) := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    ((sargosSlowQuarticMaximum M (fun _ => 1) p.1 p.2 (fun t => 4*p.2^2/p.1*t^6))^6)
  have hh := sargosQuarticParameter_source_lintegral_le_rectangle hΔ
    (by positivity : 0 ≤ 1/N^3) F
  convert hh using 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro α hα
  dsimp only
  apply lintegral_congr
  intro γ
  have hα0 : α ≠ 0 := ne_of_gt (hΔ.trans_le hα.1)
  have hφ : (fun t : ℝ => γ^2*t^6/(16*α^7)) =
      (fun t => 4*(sargosQuarticParameterMap (α,γ)).2^2/
        (sargosQuarticParameterMap (α,γ)).1*t^6) := by
    funext t
    exact sargosQuarticParameterMap_sextic hα0 γ t
  rw [hφ]
  rfl

end TaoTrudgianYang2025
