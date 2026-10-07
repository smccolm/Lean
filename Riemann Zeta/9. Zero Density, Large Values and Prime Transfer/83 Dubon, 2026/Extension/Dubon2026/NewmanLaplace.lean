import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Actual bounded-function Laplace transforms and Tauberian contour bounds -/

namespace Dubon2026

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The genuine one-sided Laplace integral. -/
def newmanLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, f t * Complex.exp (-z * t)

/-- The genuine finite Laplace integral on the positive interval. -/
def newmanTruncatedLaplace (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioc 0 T, f t * Complex.exp (-z * t)

/-- The actual Laplace integrand has the real exponential norm dictated by Re(z). -/
theorem norm_newmanLaplace_integrand (f : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    ‖f t * Complex.exp (-z * t)‖ = ‖f t‖ * Real.exp (-z.re * t) := by
  simp [Complex.norm_exp]

/-- Bounded measurable data give an integrable actual Laplace transform in the right half-plane. -/
theorem newmanLaplace_integrable {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => f t * Complex.exp (-z * t)) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (show -z.re < 0 by linarith) 0).const_mul B).mono'
  · exact hfm.restrict.mul (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_newmanLaplace_integrand]
    exact mul_le_mul_of_nonneg_right (hf t ht.le) (Real.exp_pos _).le

/-- On any finite positive interval the actual truncated transform is integrable for every complex parameter. -/
theorem newmanTruncatedLaplace_integrable {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (T : ℝ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => f t * Complex.exp (-z * t)) (Ioc 0 T) := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hf 0 le_rfl)
  have hi : IntegrableOn (fun _ : ℝ => B * Real.exp (|z.re| * T)) (Ioc 0 T) :=
    continuousOn_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply hi.mono'
  · exact hfm.restrict.mul (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * t))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_newmanLaplace_integrand]
    apply mul_le_mul (hf t ht.1.le) ?_ (Real.exp_pos _).le hB
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (neg_le_abs z.re) ht.1.le).trans
      (mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _))

/-- The genuine full-minus-truncated transform is exactly the positive tail integral. -/
theorem newmanLaplace_sub_truncated {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 0 < z.re) :
    newmanLaplace f z - newmanTruncatedLaplace f T z =
      ∫ t : ℝ in Ioi T, f t * Complex.exp (-z * t) := by
  have hh := intervalIntegral.integral_Ioi_sub_Ioi (newmanLaplace_integrable hfm hf hz) hT
  rw [intervalIntegral.integral_of_le hT] at hh
  dsimp only [newmanLaplace, newmanTruncatedLaplace]
  linear_combination hh

/-- The actual Laplace tail obeys the exponentially decaying bound needed on the right contour. -/
theorem norm_newmanLaplace_tail_le {f : ℝ → ℂ} {B : ℝ}
    (hfm : AEStronglyMeasurable f volume) (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : 0 < z.re) :
    ‖newmanLaplace f z - newmanTruncatedLaplace f T z‖ ≤
      B * Real.exp (-z.re * T) / z.re := by
  rw [newmanLaplace_sub_truncated hfm hf hT hz]
  calc
    _ ≤ ∫ t : ℝ in Ioi T, B * Real.exp (-z.re * t) := by
      apply norm_integral_le_of_norm_le ((integrableOn_exp_mul_Ioi (by linarith : -z.re < 0) T).const_mul B)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_newmanLaplace_integrand]
      exact mul_le_mul_of_nonneg_right (hf t (hT.trans ht.le)) (Real.exp_pos _).le
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -z.re < 0) T]; ring

/-- The actual truncated transform has the complementary exponential bound on the left contour. -/
theorem norm_newmanTruncatedLaplace_left_le {f : ℝ → ℂ} {B : ℝ}
    (hf : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B) {T : ℝ} {z : ℂ} (hz : z.re < 0) :
    ‖newmanTruncatedLaplace f T z‖ ≤ B * Real.exp (-z.re * T) / (-z.re) := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hf 0 le_rfl)
  have hi : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Iic T) :=
    (integrableOn_exp_mul_Iic (show 0 < -z.re by linarith) T).const_mul B
  calc
    _ ≤ ∫ t : ℝ in Ioc 0 T, B * Real.exp (-z.re * t) := by
      apply norm_integral_le_of_norm_le (hi.mono_set Ioc_subset_Iic_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [norm_newmanLaplace_integrand]
      exact mul_le_mul_of_nonneg_right (hf t ht.1.le) (Real.exp_pos _).le
    _ ≤ ∫ t : ℝ in Iic T, B * Real.exp (-z.re * t) :=
      setIntegral_mono_set hi (.of_forall (fun _ => mul_nonneg hB (Real.exp_pos _).le))
        Ioc_subset_Iic_self.eventuallyLE
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic (by linarith : 0 < -z.re) T]; ring

end
end Dubon2026
