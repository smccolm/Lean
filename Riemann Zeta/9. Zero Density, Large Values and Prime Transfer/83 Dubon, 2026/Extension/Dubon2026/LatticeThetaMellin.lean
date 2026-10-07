import Dubon2026.LatticeThetaDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # The genuine upper-tail Mellin integral of the lattice theta remainder -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set
open scoped Topology

noncomputable section

/-- The literal complex Mellin integrand of the actual nonzero lattice theta series. -/
def latticeThetaMellinKernel (z : ℍ) (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * (latticeThetaRemainder z t : ℂ)

/-- The actual upper-tail integral used in the completed Epstein continuation. -/
def latticeThetaMellinTail (z : ℍ) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1, latticeThetaMellinKernel z s t

/-- Every real power times a decaying exponential is integrable away from zero. -/
theorem integrableOn_rpow_exp_tail (r : ℝ) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ r * Real.exp (-b * t)) (Ioi 1) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := max 0 r) (p := 1)
    (by have := le_max_left (0 : ℝ) r; linarith) le_rfl hb
  simp only [Real.rpow_one, neg_mul] at hi
  refine (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).mono' ?_ ?_
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply continuousOn_of_forall_continuousAt
    intro t ht
    change 1 < t at ht
    exact (Real.continuousAt_rpow_const t r (Or.inl (by linarith : t ≠ 0))).mul
      (Real.continuous_exp.continuousAt.comp (continuousAt_const.mul continuousAt_id))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.exp_pos _).le)]
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le ht.le (le_max_right (0 : ℝ) r))
      (Real.exp_pos (-b * t)).le

/-- The actual Mellin integrand is measurable on its integration domain. -/
theorem aestronglyMeasurable_latticeThetaMellinKernel (z : ℍ) (s : ℂ) :
    AEStronglyMeasurable (latticeThetaMellinKernel z s) (volume.restrict (Ioi 1)) := by
  have hc : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 1) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    change 1 < t at ht
    exact Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr (by linarith : t ≠ 0))
  exact (hc.aestronglyMeasurable measurableSet_Ioi).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_latticeThetaRemainder z)).aestronglyMeasurable

/-- The actual Mellin integrand has its exact real power and positive theta-tail norm. -/
theorem norm_latticeThetaMellinKernel (z : ℍ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖latticeThetaMellinKernel z s t‖ = t ^ (s.re - 1) * latticeThetaRemainder z t := by
  rw [latticeThetaMellinKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_of_nonneg (latticeThetaRemainder_nonneg z t)]
  simp only [Complex.sub_re, Complex.one_re]

/-- The genuine upper-tail Mellin integral converges absolutely at every complex parameter. -/
theorem integrableOn_latticeThetaMellinKernel (z : ℍ) (s : ℂ) :
    IntegrableOn (latticeThetaMellinKernel z s) (Ioi 1) := by
  have hb : 0 < Real.pi * latticeQuadraticLower z / 2 :=
    div_pos (mul_pos Real.pi_pos (latticeQuadraticLower_pos z)) (by norm_num)
  apply ((integrableOn_rpow_exp_tail (s.re - 1) hb).mul_const
    (latticeThetaRemainder z (1 / 2))).mono'
      (aestronglyMeasurable_latticeThetaMellinKernel z s)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 1 < t at ht
  rw [norm_latticeThetaMellinKernel z s (by linarith : 0 < t), mul_assoc]
  exact mul_le_mul_of_nonneg_left (latticeThetaRemainder_decay z ht.le)
    (Real.rpow_nonneg (by linarith) _)

/-- The actual parameter derivative of the upper-tail Mellin kernel. -/
theorem hasDerivAt_latticeThetaMellinKernel (z : ℍ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun w : ℂ => latticeThetaMellinKernel z w t)
      (latticeThetaMellinKernel z s t * (Real.log t : ℂ)) s := by
  have h := (((hasDerivAt_id s).sub_const 1).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr ht.ne'))).mul_const (latticeThetaRemainder z t : ℂ)
  convert h using 1
  rw [Complex.ofReal_log ht.le]
  simp only [latticeThetaMellinKernel, mul_one, id_eq]
  ring

end
end Dubon2026
