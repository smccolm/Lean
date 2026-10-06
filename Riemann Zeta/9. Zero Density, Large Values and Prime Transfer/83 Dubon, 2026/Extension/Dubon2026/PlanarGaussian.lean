import Dubon2026.InverseCharacteristic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Normalized planar Gaussian kernels and their inverse characteristic integrals -/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace

noncomputable section

/-- A centered planar Gaussian kernel of total mass one when `c > 0`. -/
def planarGaussian (c : ℝ) (x : ℂ) : ℝ :=
  (c / Real.pi) * Real.exp (-c * ‖x‖ ^ 2)

theorem planarGaussian_nonneg {c : ℝ} (hc : 0 ≤ c) (x : ℂ) :
    0 ≤ planarGaussian c x := by
  unfold planarGaussian
  positivity

theorem continuous_planarGaussian (c : ℝ) : Continuous (planarGaussian c) := by
  unfold planarGaussian
  fun_prop

theorem integrable_planarGaussian {c : ℝ} (hc : 0 < c) :
    Integrable (planarGaussian c) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (c : ℂ)) (by simpa using hc) 0 0).re
  have he : Integrable (fun x : ℂ => Real.exp (-c * ‖x‖ ^ 2)) := by
    convert h using 1
    ext x
    rw [zero_mul, add_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg,
      ← Complex.ofReal_mul, ← Complex.ofReal_exp]
    rfl
  exact he.const_mul _

theorem integral_planarGaussian {c : ℝ} (hc : 0 < c) :
    ∫ x : ℂ, planarGaussian c x = 1 := by
  unfold planarGaussian
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hc]
  simp only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0),
    Real.rpow_one]
  field_simp

theorem planarGaussian_le {c : ℝ} (hc : 0 ≤ c) (x : ℂ) :
    planarGaussian c x ≤ c / Real.pi := by
  unfold planarGaussian
  apply mul_le_of_le_one_right (by positivity)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _))

/-- Inverse integral of a Gaussian damping factor, in the characteristic convention. -/
theorem inverse_integral_gaussian {c : ℝ} (hc : 0 < c) (x : ℂ) :
    planarInverseCharacteristic
      (fun ξ : ℂ => Complex.exp (-((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2)) x =
      (planarGaussian c x : ℂ) := by
  unfold planarInverseCharacteristic inverseCharacteristicKernel planarGaussian
  simp_rw [← Complex.exp_add]
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := ℂ) (b := (((4 * c)⁻¹ : ℝ) : ℂ))
    (by simpa using (show 0 < (4 * c)⁻¹ by positivity)) (-Complex.I) x
  have hi : (∫ ξ : ℂ, Complex.exp (-Complex.I * (inner ℝ x ξ : ℝ) +
      -((4 * c)⁻¹ : ℝ) * ‖ξ‖ ^ 2)) =
      ((Real.pi : ℂ) / (((4 * c)⁻¹ : ℝ) : ℂ)) *
        Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
    convert h using 1
    · congr 1
      ext ξ
      congr 1
      ring
    · simp only [Complex.finrank_real_complex, Nat.cast_ofNat,
        div_self (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
      congr 1
      congr 1
      push_cast
      simp only [neg_sq, Complex.I_sq]
      field_simp
  rw [hi, Complex.real_smul]
  push_cast
  rw [← mul_assoc]
  congr 1
  field_simp
  ring

end

end Dubon2026
