import Dubon2026.NewmanLaplace

/-! # Entire dependence of the actual truncated Laplace transform -/

namespace Dubon2026

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- Differentiation under the genuine finite integral uses a proved constant majorant on each parameter ball. -/
theorem hasDerivAt_newmanTruncatedLaplace {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    HasDerivAt (newmanTruncatedLaplace f T)
      (∫ t : ℝ in Ioc 0 T, f t * (-(t : ℂ)) * Complex.exp (-z * t)) z := by
  let F : ℂ → ℝ → ℂ := fun w t => f t * Complex.exp (-w * t)
  let F' : ℂ → ℝ → ℂ := fun w t => f t * (-(t : ℂ)) * Complex.exp (-w * t)
  let C : ℝ := B * T * Real.exp ((‖z‖ + 1) * T)
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hf 0 le_rfl)
  have hmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) (volume.restrict (Ioc 0 T)) :=
    .of_forall (fun w => hfm.restrict.mul
      (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-w * t))).aestronglyMeasurable)
  have hdmeas : AEStronglyMeasurable (F' z) (volume.restrict (Ioc 0 T)) := by
    exact (hfm.restrict.mul (by fun_prop : Continuous (fun t : ℝ => -(t : ℂ))).aestronglyMeasurable).mul
      (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * t))).aestronglyMeasurable
  have hi : Integrable (fun _ : ℝ => C) (volume.restrict (Ioc 0 T)) :=
    continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc 0 T)),
      ∀ w ∈ Metric.ball z 1, ‖F' w t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro w hw
    have hw' : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hwn : ‖w‖ ≤ ‖z‖ + 1 := by
      have hh' : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by simpa using norm_add_le (w - z) z
      linarith
    have hwre : -w.re ≤ ‖z‖ + 1 :=
      (neg_le_abs w.re).trans ((Complex.abs_re_le_norm w).trans hwn)
    have hexp : Real.exp (-w.re * t) ≤ Real.exp ((‖z‖ + 1) * T) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_right hwre ht.1.le).trans
        (mul_le_mul_of_nonneg_left ht.2 (by positivity))
    dsimp only [F', C]
    simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1.le, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_le_mul (mul_le_mul (hf t ht.1.le) ht.2 ht.1.le hB) hexp
      (Real.exp_pos _).le (mul_nonneg hB hT)
  have hd : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc 0 T)), ∀ w ∈ Metric.ball z 1,
      HasDerivAt (F · t) (F' w t) w := by
    apply Filter.Eventually.of_forall
    intro t w _
    dsimp only [F, F']
    convert ((Complex.hasDerivAt_exp (-w * t)).comp w
      ((hasDerivAt_id w).neg.mul_const (t : ℂ))).const_mul (f t) using 1
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z (by norm_num : (0 : ℝ) < 1)) hmeas
    (newmanTruncatedLaplace_integrable hfm hf T z) hdmeas hb hi hd).2

/-- The literal truncated Laplace transform is entire for every positive truncation. -/
theorem differentiable_newmanTruncatedLaplace {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    {T : ℝ} (hT : 0 ≤ T) : Differentiable ℂ (newmanTruncatedLaplace f T) :=
  fun z => (hasDerivAt_newmanTruncatedLaplace hfm hf hT z).differentiableAt

end
end Dubon2026
