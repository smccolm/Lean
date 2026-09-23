import TaoTrudgianYang2025.SargosKernelFourier

/-! Pointwise kernel majorization on the actual centered real windows. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargos_sinc_lower {x : ℝ} (hx : |x| ≤ Real.pi/2) :
    1/2 ≤ Real.sinc x := by
  by_cases hz : x = 0
  · norm_num [hz]
  have habs : 0 < |x| := abs_pos.mpr hz
  have hsin := Real.mul_le_sin (abs_nonneg x) hx
  have hsinc : 2/Real.pi ≤ Real.sinc |x| := by
    rw [Real.sinc_of_ne_zero (ne_of_gt habs)]
    exact (le_div_iff₀ habs).mpr hsin
  have he : Real.sinc |x| = Real.sinc x := by
    by_cases hpos : 0 ≤ x
    · rw [abs_of_nonneg hpos]
    · rw [abs_of_neg (lt_of_not_ge hpos),Real.sinc_neg]
  rw [he] at hsinc
  have hhalf : (1/2 : ℝ) ≤ 2/Real.pi := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    linarith [Real.pi_le_four]
  exact hhalf.trans hsinc

theorem sargosSincKernel_lower {w x : ℝ} (hw : 0 < w)
    (hx : w*|x| ≤ 1/2) : w/4 ≤ sargosSincKernel w x := by
  have harg : |Real.pi*w*x| ≤ Real.pi/2 := by
    rw [abs_mul,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos hw]
    nlinarith [mul_le_mul_of_nonneg_left hx Real.pi_pos.le]
  have hs := sargos_sinc_lower harg
  have hsq : (1/4 : ℝ) ≤ Real.sinc (Real.pi*w*x)^2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq hw.le
  simpa only [sargosSincKernel,div_eq_mul_inv,one_mul] using h

theorem sargosSincKernel_rectangle_lower {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : a*|x| ≤ 1/2) (hy : b*|y| ≤ 1/2) :
    a*b/16 ≤ sargosSincKernel a x*sargosSincKernel b y := by
  calc
    _ = (a/4)*(b/4) := by ring
    _ ≤ _ := mul_le_mul (sargosSincKernel_lower ha hx) (sargosSincKernel_lower hb hy)
      (by positivity) (sargosSincKernel_nonneg ha.le x)

theorem sargos_window_scale_control {δ c x : ℝ} (hδ : 0 < δ)
    (hx : x ∈ Set.Icc c (c+δ)) :
    (1/δ)*|x-(c+δ/2)| ≤ 1/2 := by
  have habs : |x-(c+δ/2)| ≤ δ/2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2]
  rw [one_div,inv_mul_eq_div]
  apply (div_le_iff₀ hδ).mpr
  linarith

theorem sargosSincKernel_window_rectangle {δ lambda c d α γ : ℝ}
    (hδ : 0 < δ) (hlambda : 0 < lambda)
    (hα : α ∈ Set.Icc c (c+δ)) (hγ : γ ∈ Set.Icc d (d+lambda)) :
    1/(16*δ*lambda) ≤
      sargosSincKernel (1/δ) (α-(c+δ/2))*
        sargosSincKernel (1/lambda) (γ-(d+lambda/2)) := by
  have h := sargosSincKernel_rectangle_lower (one_div_pos.mpr hδ) (one_div_pos.mpr hlambda)
    (sargos_window_scale_control hδ hα) (sargos_window_scale_control hlambda hγ)
  convert h using 1
  ring

end TaoTrudgianYang2025
