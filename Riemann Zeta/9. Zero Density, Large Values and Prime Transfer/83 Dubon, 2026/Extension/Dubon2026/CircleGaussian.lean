import Dubon2026.CircleMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # A quantitative Gaussian bound for the actual circle characteristic integral -/

namespace Dubon2026

open MeasureTheory

theorem integral_circle_quadratic (c u : ℝ) :
    (∫ z : UnitAddCircle, 1 - c * (u * (fourier 1 z).re) ^ 2
      ∂AddCircle.haarAddCircle) = 1 - c * u ^ 2 / 2 := by
  have hi : Integrable (fun z : UnitAddCircle => (fourier 1 z).re ^ 2)
      AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun z : UnitAddCircle => (fourier 1 z).re ^ 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_pow, ← mul_assoc]
  rw [integral_sub (integrable_const 1) (hi.const_mul _), integral_const_mul,
    integral_circle_realPart_sq]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem circleCharacteristic_re_lower (u : ℝ) :
    1 - u ^ 2 / 4 ≤ (circleCharacteristic u).re := by
  rw [circleCharacteristic_re_eq_cos]
  have hi : Integrable (fun z : UnitAddCircle => 1 - (1 / 2 : ℝ) *
      (u * (fourier 1 z).re) ^ 2) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun z : UnitAddCircle => 1 - (1 / 2 : ℝ) *
      (u * (fourier 1 z).re) ^ 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun z : UnitAddCircle => Real.cos (u * (fourier 1 z).re))
      AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun z : UnitAddCircle => Real.cos (u * (fourier 1 z).re))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono hi hj (fun z => by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      (Real.one_sub_sq_div_two_le_cos (x := u * (fourier 1 z).re)))
  rw [integral_circle_quadratic] at hh
  convert hh using 1
  ring

theorem circleCharacteristic_re_upper {u : ℝ} (hu : |u| ≤ 1) :
    (circleCharacteristic u).re ≤ 1 - u ^ 2 / Real.pi ^ 2 := by
  rw [circleCharacteristic_re_eq_cos]
  have hi : Integrable (fun z : UnitAddCircle => Real.cos (u * (fourier 1 z).re))
      AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun z : UnitAddCircle => Real.cos (u * (fourier 1 z).re))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun z : UnitAddCircle => 1 - (2 / Real.pi ^ 2) *
      (u * (fourier 1 z).re) ^ 2) AddCircle.haarAddCircle :=
    (by fun_prop : Continuous (fun z : UnitAddCircle => 1 - (2 / Real.pi ^ 2) *
      (u * (fourier 1 z).re) ^ 2)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono hi hj (fun z =>
    Real.cos_le_one_sub_mul_cos_sq (by
      rw [abs_mul]
      calc
        |u| * |(fourier 1 z).re| ≤ 1 * 1 :=
          mul_le_mul hu (abs_circle_realPart_le_one z) (abs_nonneg _) zero_le_one
        _ ≤ Real.pi := by nlinarith [Real.two_le_pi]))
  rw [integral_circle_quadratic] at hh
  convert hh using 1
  ring

theorem norm_circleCharacteristic_le_gaussian {u : ℝ} (hu : |u| ≤ 1) :
    ‖circleCharacteristic u‖ ≤ Real.exp (-u ^ 2 / Real.pi ^ 2) := by
  have hu2 : u ^ 2 ≤ 1 := by
    have hh := mul_le_mul hu hu (abs_nonneg u) zero_le_one
    simpa only [← sq, sq_abs, one_pow] using hh
  have hp : 0 ≤ (circleCharacteristic u).re := by
    nlinarith [circleCharacteristic_re_lower u]
  rw [norm_circleCharacteristic_eq_abs_re, abs_of_nonneg hp]
  exact (circleCharacteristic_re_upper hu).trans (by
    convert Real.add_one_le_exp (-u ^ 2 / Real.pi ^ 2) using 1
    ring)

end Dubon2026
