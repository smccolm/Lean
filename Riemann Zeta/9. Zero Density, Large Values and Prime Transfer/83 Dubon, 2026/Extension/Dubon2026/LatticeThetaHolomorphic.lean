import Dubon2026.LatticeThetaMellin

/-! # Entire dependence of the actual upper-tail lattice Mellin integral -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set
open scoped Topology

noncomputable section

/-- The true Mellin derivative has an integrable exponential majorant on every bounded real-parameter strip. -/
theorem norm_latticeThetaMellin_derivative_le (z : ℍ) {s : ℂ} {A t : ℝ}
    (hs : s.re ≤ A) (ht : 1 ≤ t) :
    ‖latticeThetaMellinKernel z s t * (Real.log t : ℂ)‖ ≤
      (t ^ A * Real.exp (-(Real.pi * latticeQuadraticLower z / 2) * t)) *
        latticeThetaRemainder z (1 / 2) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [norm_mul, norm_latticeThetaMellinKernel z s ht0,
    Complex.norm_of_nonneg (Real.log_nonneg ht)]
  have hp : t ^ (s.re - 1) * t = t ^ s.re := by
    calc
      t ^ (s.re - 1) * t = t ^ (s.re - 1) * t ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = t ^ ((s.re - 1) + 1) := (Real.rpow_add ht0 _ _).symm
      _ = t ^ s.re := by congr 1; ring
  calc
    t ^ (s.re - 1) * latticeThetaRemainder z t * Real.log t =
        (t ^ (s.re - 1) * Real.log t) * latticeThetaRemainder z t := by ring
    _ ≤ (t ^ (s.re - 1) * t) * latticeThetaRemainder z t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.log_le_self ht0.le) (Real.rpow_nonneg ht0.le _))
        (latticeThetaRemainder_nonneg z t)
    _ = t ^ s.re * latticeThetaRemainder z t := by rw [hp]
    _ ≤ t ^ A * latticeThetaRemainder z t :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le ht hs)
        (latticeThetaRemainder_nonneg z t)
    _ ≤ t ^ A * (Real.exp (-(Real.pi * latticeQuadraticLower z / 2) * t) *
        latticeThetaRemainder z (1 / 2)) :=
      mul_le_mul_of_nonneg_left (latticeThetaRemainder_decay z ht) (Real.rpow_nonneg ht0.le _)
    _ = _ := by ring

/-- Differentiation under the actual upper-tail integral is justified by the proved exponential bound. -/
theorem hasDerivAt_latticeThetaMellinTail (z : ℍ) (s : ℂ) :
    HasDerivAt (latticeThetaMellinTail z)
      (∫ t : ℝ in Ioi 1, latticeThetaMellinKernel z s t * (Real.log t : ℂ)) s := by
  have hb : 0 < Real.pi * latticeQuadraticLower z / 2 :=
    div_pos (mul_pos Real.pi_pos (latticeQuadraticLower_pos z)) (by norm_num)
  have hm : AEStronglyMeasurable
      (fun t : ℝ => latticeThetaMellinKernel z s t * (Real.log t : ℂ))
      (volume.restrict (Ioi 1)) :=
    (aestronglyMeasurable_latticeThetaMellinKernel z s).mul
      (Complex.continuous_ofReal.measurable.comp Real.measurable_log).aestronglyMeasurable
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w t => latticeThetaMellinKernel z w t)
    (F' := fun w t => latticeThetaMellinKernel z w t * (Real.log t : ℂ))
    (bound := fun t : ℝ => (t ^ (s.re + 1) *
      Real.exp (-(Real.pi * latticeQuadraticLower z / 2) * t)) * latticeThetaRemainder z (1 / 2))
    (Metric.ball_mem_nhds s (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun w => aestronglyMeasurable_latticeThetaMellinKernel z w))
    (integrableOn_latticeThetaMellinKernel z s) hm ?_
    ((integrableOn_rpow_exp_tail (s.re + 1) hb).mul_const (latticeThetaRemainder z (1 / 2))) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    apply norm_latticeThetaMellin_derivative_le z _ ht.le
    have hd : ‖w - s‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
    have hr := Complex.re_le_norm (w - s)
    simp only [Complex.sub_re] at hr
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w _
    exact hasDerivAt_latticeThetaMellinKernel z w (lt_trans zero_lt_one ht)

/-- The actual upper-tail lattice Mellin integral is entire. -/
theorem differentiable_latticeThetaMellinTail (z : ℍ) :
    Differentiable ℂ (latticeThetaMellinTail z) :=
  fun s => (hasDerivAt_latticeThetaMellinTail z s).differentiableAt

end
end Dubon2026
