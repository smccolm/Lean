import TaoTrudgianYang2025.NeumannContourKernel

/-!
# Passing the Neumann rectangle to infinite vertical rays

Every ray is absolutely integrable, including the limiting ray through
one. The upper horizontal side is shown to vanish before the contour
identity is passed to the limit.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open scoped Interval

namespace TaoTrudgianYang2025

def neumannVerticalIntegral (x b : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, neumannContourKernel x ((b : ℂ) + t * I)

theorem norm_neumannContourKernel_horizontal_integral_le {x b H : ℝ}
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (hH : 1 ≤ H) :
    ‖∫ u in (0 : ℝ)..b, neumannContourKernel x ((u : ℂ) + H * I)‖ ≤ Real.exp (-x * H) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := b) (C := Real.exp (-x * H))
    (f := fun u : ℝ => neumannContourKernel x ((u : ℂ) + H * I))
    (fun u _ => norm_neumannContourKernel_horizontal_le (u := u) hH)
  rw [sub_zero, abs_of_nonneg hb] at h
  exact h.trans (by nlinarith [Real.exp_pos (-x * H)])

theorem tendsto_neumannContourKernel_horizontal_integral {x b : ℝ}
    (hx : 0 < x) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Tendsto (fun H : ℝ =>
      ∫ u in (0 : ℝ)..b, neumannContourKernel x ((u : ℂ) + H * I)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun H : ℝ => -x * H) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hx)
  have hexp := Real.tendsto_exp_atBot.comp hlin
  apply squeeze_zero_norm' _ hexp
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with H hH
  exact norm_neumannContourKernel_horizontal_integral_le hb hb1 hH

theorem neumannContourKernel_infinite_rectangle {x b : ℝ}
    (hx : 0 < x) (hb : 0 ≤ b) (hb1 : b < 1) :
    (∫ u in (0 : ℝ)..b, neumannContourKernel x u) =
      I * neumannVerticalIntegral x 0 - I * neumannVerticalIntegral x b := by
  have hl := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrableOn_neumannContourKernel_vertical hx (le_refl (0 : ℝ))) tendsto_id
  have hr := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrableOn_neumannContourKernel_vertical hx hb) tendsto_id
  have hh := tendsto_neumannContourKernel_horizontal_integral hx hb hb1.le
  have heq : ∀ H : ℝ,
      (∫ u in (0 : ℝ)..b, neumannContourKernel x u) -
        (∫ u in (0 : ℝ)..b, neumannContourKernel x ((u : ℂ) + H * I)) +
        I * (∫ t in (0 : ℝ)..H, neumannContourKernel x ((b : ℂ) + t * I)) -
        I * (∫ t in (0 : ℝ)..H, neumannContourKernel x ((0 : ℂ) + t * I)) = 0 := by
    intro H
    simpa only [zero_add] using neumannContourKernel_finite_rectangle x hb hb1 (H := H)
  have ht := (((tendsto_const_nhds (x :=
    ∫ u in (0 : ℝ)..b, neumannContourKernel x u)).sub hh).add
      (hr.const_mul I)).sub (hl.const_mul I)
  have hz : (∫ u in (0 : ℝ)..b, neumannContourKernel x u) -
      0 + I * neumannVerticalIntegral x b - I * neumannVerticalIntegral x 0 = 0 := by
    exact tendsto_nhds_unique ht (by simpa only [id_eq, Complex.ofReal_zero, heq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0)))
  linear_combination hz

end TaoTrudgianYang2025
