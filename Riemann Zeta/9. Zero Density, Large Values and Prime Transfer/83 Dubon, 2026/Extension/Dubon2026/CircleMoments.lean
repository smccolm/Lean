import Dubon2026.CircleCharacteristic

/-! # Exact Haar moments of the real coordinate of a unit-circle point -/

namespace Dubon2026

open MeasureTheory
open scoped ComplexConjugate

theorem integrable_circle_fourier (n : ℤ) :
    Integrable (fourier n : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
  (fourier n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_circle_fourier (n : ℤ) :
    (∫ z : UnitAddCircle, fourier n z ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have hh := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using hh

theorem circle_realPart_sq_expansion (z : UnitAddCircle) :
    (((fourier 1 z).re ^ 2 : ℝ) : ℂ) = (fourier 2 z + 2 + fourier (-2) z) / 4 := by
  rw [Complex.ofReal_pow, Complex.re_eq_add_conj, ← fourier_neg]
  have hprod : fourier 1 z * fourier (-1) z = 1 := by
    rw [← fourier_add]
    norm_num [fourier_zero]
  have hpos : fourier 1 z * fourier 1 z = fourier 2 z := by
    rw [← fourier_add]
    norm_num
  have hneg : fourier (-1) z * fourier (-1) z = fourier (-2) z := by
    rw [← fourier_add]
    norm_num
  calc
    _ = (fourier 1 z * fourier 1 z + 2 * (fourier 1 z * fourier (-1) z) +
        fourier (-1) z * fourier (-1) z) / 4 := by ring
    _ = _ := by rw [hprod, hpos, hneg, mul_one]

theorem integral_circle_realPart_sq :
    (∫ z : UnitAddCircle, (fourier 1 z).re ^ 2 ∂AddCircle.haarAddCircle) = 1 / 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [circle_realPart_sq_expansion]
  have hi : Integrable (fun z : UnitAddCircle => fourier 2 z + 2) AddCircle.haarAddCircle :=
    (integrable_circle_fourier 2).add (integrable_const 2)
  rw [integral_div, integral_add hi
    (integrable_circle_fourier (-2)), integral_add (integrable_circle_fourier 2) (integrable_const 2)]
  rw [integral_circle_fourier 2, integral_circle_fourier (-2)]
  norm_num

theorem abs_circle_realPart_le_one (z : UnitAddCircle) : |(fourier 1 z).re| ≤ 1 := by
  have hh := Complex.abs_re_le_norm (fourier 1 z)
  simpa only [fourier_apply, Circle.norm_coe] using hh

theorem circleCharacteristic_re_eq_cos (u : ℝ) :
    (circleCharacteristic u).re =
      ∫ z : UnitAddCircle, Real.cos (u * (fourier 1 z).re) ∂AddCircle.haarAddCircle := by
  have hr := integral_re (integrable_circleExponential u)
  change (∫ z : UnitAddCircle, (circleExponential u z).re ∂AddCircle.haarAddCircle) =
    (circleCharacteristic u).re at hr
  rw [← hr]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change (Complex.exp (Complex.I * ((u * (fourier 1 z).re : ℝ) : ℂ))).re = _
  rw [mul_comm, Complex.exp_ofReal_mul_I_re]

theorem norm_circleCharacteristic_eq_abs_re (u : ℝ) :
    ‖circleCharacteristic u‖ = |(circleCharacteristic u).re| := by
  have he : circleCharacteristic u = ((circleCharacteristic u).re : ℂ) := by
    apply Complex.ext <;> simp [circleCharacteristic_im]
  conv_lhs => rw [he]
  simp only [Complex.norm_real, Real.norm_eq_abs]

end Dubon2026
