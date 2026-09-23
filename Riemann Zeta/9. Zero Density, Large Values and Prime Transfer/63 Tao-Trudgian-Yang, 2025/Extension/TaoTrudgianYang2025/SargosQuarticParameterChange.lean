import TaoTrudgianYang2025.SargosQuarticParameterDomain

/-! Genuine one-variable substitutions for the triangular quartic parameter map. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuarticParameter_horizontal_lintegral {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (G : ℝ → ℝ≥0∞) :
    (∫⁻ α in Icc a b, G α) =
      ∫⁻ x in Icc (1/(4*b)) (1/(4*a)),
        ENNReal.ofReal (1/(4*x^2))*G (1/(4*x)) := by
  have hb : 0 < b := ha.trans_le hab
  have hpos : ∀ x ∈ Icc (1/(4*b)) (1/(4*a)), 0 < x := by
    intro x hx
    exact (by positivity : 0 < 1/(4*b)).trans_le hx.1
  have hi : InjOn (fun x : ℝ => 1/(4*x)) (Icc (1/(4*b)) (1/(4*a))) := by
    intro x _ y _ he
    have hh : 4*x = 4*y := inv_injective (by simpa only [one_div] using he)
    linarith only [hh]
  rw [← sargosQuarticParameter_horizontal_image ha hab]
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
    (fun x hx => (sargosQuarticParameter_reciprocal_deriv (ne_of_gt (hpos x hx))).hasDerivWithinAt)
    hi G
  convert hh using 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro x hx
  dsimp only
  simp only [neg_div,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(4*x^2))]

theorem sargosQuarticParameter_vertical_lintegral {x : ℝ} (hx : 0 < x)
    (H : ℝ) (G : ℝ → ℝ≥0∞) :
    (∫⁻ γ in Icc (-H) H, G γ) =
      ∫⁻ y in Icc (-16*H*x^4) (16*H*x^4),
        ENNReal.ofReal (1/(16*x^4))*G (-y/(16*x^4)) := by
  have hx4 : 16*x^4 ≠ 0 := by positivity
  have hi : InjOn (fun y : ℝ => -y/(16*x^4)) (Icc (-16*H*x^4) (16*H*x^4)) := by
    intro y _ z _ he
    exact neg_injective ((div_left_inj' hx4).mp he)
  rw [← sargosQuarticParameter_vertical_image hx H]
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Icc
    (fun y _ => (sargosQuarticParameter_vertical_deriv x y).hasDerivWithinAt) hi G
  convert hh using 1
  apply setLIntegral_congr_fun measurableSet_Icc
  intro y hy
  dsimp only
  simp only [neg_div,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(16*x^4))]

end TaoTrudgianYang2025
