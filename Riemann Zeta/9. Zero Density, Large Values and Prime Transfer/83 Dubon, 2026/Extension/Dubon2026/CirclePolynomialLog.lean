import Dubon2026.TorusPolynomial
import Mathlib.Analysis.Polynomial.MahlerMeasure

/-! # One-variable logarithmic integrability with the exact Haar normalization -/

namespace Dubon2026

open MeasureTheory
open scoped Real

noncomputable section

theorem unitCircle_volume_eq_haar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1))

instance unitCircleHaarNoAtoms : NoAtoms (AddCircle.haarAddCircle (T := 1)) where
  measure_singleton z := by
    rw [← unitCircle_volume_eq_haar, ← Metric.closedBall_zero, AddCircle.volume_closedBall]
    norm_num

theorem fourier_one_eq_circleMap (t : ℝ) :
    fourier 1 (t : UnitAddCircle) = circleMap 0 1 (2 * Real.pi * t) := by
  rw [fourier_coe_apply]
  simp only [circleMap, zero_add, one_mul, Int.cast_one, Complex.ofReal_one, div_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  congr 1
  ring

theorem integrable_polynomial_log_circle (p : Polynomial ℂ) :
    Integrable (fun z : UnitAddCircle => Real.log ‖p.eval (fourier 1 z)‖)
      AddCircle.haarAddCircle := by
  have hc : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hi := p.intervalIntegrable_mahlerMeasure.comp_mul_left (c := 2 * Real.pi)
  simp only [zero_div, div_self hc] at hi
  have hpull : IntervalIntegrable
      (fun t : ℝ => Real.log ‖p.eval (fourier 1 (t : UnitAddCircle))‖) volume 0 1 := by
    simpa only [fourier_one_eq_circleMap] using hi
  have hm : Measurable (fun z : UnitAddCircle => Real.log ‖p.eval (fourier 1 z)‖) :=
    Real.measurable_log.comp ((p.continuous.comp (fourier 1).continuous).norm.measurable)
  have hp := (AddCircle.measurePreserving_mk (1 : ℝ) 0).integrable_comp hm.aestronglyMeasurable
  rw [zero_add] at hp
  have hv := hp.mp hpull.1
  rwa [unitCircle_volume_eq_haar] at hv

theorem integral_polynomial_log_circle (p : Polynomial ℂ) :
    (∫ z : UnitAddCircle, Real.log ‖p.eval (fourier 1 z)‖ ∂AddCircle.haarAddCircle) =
      p.logMahlerMeasure := by
  rw [← unitCircle_volume_eq_haar,
    ← AddCircle.intervalIntegral_preimage (1 : ℝ) 0, zero_add]
  simp_rw [fourier_one_eq_circleMap]
  rw [intervalIntegral.integral_comp_mul_left
    (fun x : ℝ => Real.log ‖p.eval (circleMap 0 1 x)‖) (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  simp only [mul_zero, mul_one, Polynomial.logMahlerMeasure_def, Real.circleAverage_def,
    smul_eq_mul]

theorem log_leadingCoeff_le_integral_log_circle (p : Polynomial ℂ) :
    Real.log ‖p.leadingCoeff‖ ≤
      ∫ z : UnitAddCircle, Real.log ‖p.eval (fourier 1 z)‖ ∂AddCircle.haarAddCircle := by
  rw [integral_polynomial_log_circle, p.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots]
  apply le_add_of_nonneg_right
  exact Multiset.sum_nonneg (fun x hx => by
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Real.posLog_nonneg)

theorem fourier_one_injective : Function.Injective (fun z : UnitAddCircle => fourier 1 z) := by
  intro z w h
  apply AddCircle.injective_toCircle one_ne_zero
  exact Subtype.ext (by simpa only [fourier_one] using h)

theorem finite_polynomial_zeros_circle {p : Polynomial ℂ} (hp : p ≠ 0) :
    {z : UnitAddCircle | p.eval (fourier 1 z) = 0}.Finite := by
  exact (Polynomial.finite_setOf_isRoot hp).preimage fourier_one_injective.injOn

theorem polynomial_ne_zero_ae_circle {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᵐ z : UnitAddCircle ∂AddCircle.haarAddCircle, p.eval (fourier 1 z) ≠ 0 := by
  rw [ae_iff]
  simpa only [not_not] using (finite_polynomial_zeros_circle hp).measure_zero AddCircle.haarAddCircle

theorem log_coeff_zero_le_integral_log_circle {p : Polynomial ℂ} (hp : p.coeff 0 ≠ 0) :
    Real.log ‖p.coeff 0‖ ≤
      ∫ z : UnitAddCircle, Real.log ‖p.eval (fourier 1 z)‖ ∂AddCircle.haarAddCircle := by
  rw [integral_polynomial_log_circle, Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
  apply Real.log_le_log (norm_pos_iff.mpr hp)
  simpa using p.norm_coeff_le_choose_mul_mahlerMeasure 0

theorem integral_abs_log_circle_le (p : Polynomial ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z : UnitAddCircle, Real.log ‖p.eval (fourier 1 z)‖ ≤ C) :
    (∫ z : UnitAddCircle, |Real.log ‖p.eval (fourier 1 z)‖| ∂AddCircle.haarAddCircle) ≤
      2 * C - Real.log ‖p.leadingCoeff‖ := by
  have hi := integrable_polynomial_log_circle p
  have hb := integral_mono hi.abs ((integrable_const (2 * C)).sub hi)
    (fun z => (abs_le.mpr ⟨by linarith, by linarith [hbound z]⟩ :
      |Real.log ‖p.eval (fourier 1 z)‖| ≤ 2 * C - Real.log ‖p.eval (fourier 1 z)‖))
  simp only [Pi.sub_apply] at hb
  rw [integral_sub (integrable_const (2 * C)) hi, integral_const, probReal_univ, one_smul] at hb
  exact hb.trans (sub_le_sub_left (log_leadingCoeff_le_integral_log_circle p) (2 * C))

end

end Dubon2026
