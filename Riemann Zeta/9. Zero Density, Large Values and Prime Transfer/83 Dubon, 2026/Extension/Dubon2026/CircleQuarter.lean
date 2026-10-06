import Dubon2026.CircleMoments

/-! # Quarter-period reduction for the circle characteristic integral -/

namespace Dubon2026

open MeasureTheory

theorem integral_cos_cos_quarter (u : ℝ) :
    (∫ θ in 0..2 * Real.pi, Real.cos (u * Real.cos θ)) =
      4 * ∫ θ in 0..Real.pi / 2, Real.cos (u * Real.cos θ) := by
  let f : ℝ → ℝ := fun θ => Real.cos (u * Real.cos θ)
  have hf : Continuous f := by fun_prop
  have hs : (∫ θ in Real.pi..2 * Real.pi, f θ) = ∫ θ in 0..Real.pi, f θ := by
    have hh := intervalIntegral.integral_comp_add_right (a := 0) (b := Real.pi) f Real.pi
    simp only [zero_add, ← two_mul] at hh
    rw [← hh]
    congr 1
    funext θ
    simp [f, Real.cos_add_pi]
  have hr : (∫ θ in Real.pi / 2..Real.pi, f θ) = ∫ θ in 0..Real.pi / 2, f θ := by
    have hh := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi / 2) f Real.pi
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at hh
    rw [← hh]
    congr 1
    funext θ
    simp [f, Real.cos_sub]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) 0 Real.pi) (hf.intervalIntegrable Real.pi (2 * Real.pi))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) 0 (Real.pi / 2)) (hf.intervalIntegrable (Real.pi / 2) Real.pi)
  rw [hs] at h1
  rw [hr] at h2
  change (∫ θ in 0..2 * Real.pi, f θ) = 4 * ∫ θ in 0..Real.pi / 2, f θ
  linarith

theorem circleCharacteristic_re_eq_quarter (u : ℝ) :
    (circleCharacteristic u).re =
      (2 / Real.pi) * ∫ θ in 0..Real.pi / 2, Real.cos (u * Real.cos θ) := by
  rw [circleCharacteristic_eq_interval]
  have hi : IntervalIntegrable (fun θ : ℝ =>
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))) volume 0 (2 * Real.pi) :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)))).intervalIntegrable _ _
  have hh := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ θ in 0..2 * Real.pi,
    (Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))).re) =
    (∫ θ in 0..2 * Real.pi, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)) : ℂ).re at hh
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← hh]
  simp_rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
  rw [integral_cos_cos_quarter]
  field_simp
  ring

theorem norm_circleCharacteristic_le_quarter (u : ℝ) :
    ‖circleCharacteristic u‖ ≤ (2 / Real.pi) *
      ‖∫ θ in 0..Real.pi / 2, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))‖ := by
  have hi : IntervalIntegrable (fun θ : ℝ =>
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))) volume 0 (Real.pi / 2) :=
    (by fun_prop : Continuous (fun θ : ℝ =>
      Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)))).intervalIntegrable _ _
  have hh := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ θ in 0..Real.pi / 2,
    (Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))).re) =
    (∫ θ in 0..Real.pi / 2, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ)) : ℂ).re at hh
  simp_rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re] at hh
  rw [norm_circleCharacteristic_eq_abs_re, circleCharacteristic_re_eq_quarter,
    abs_mul, abs_of_pos (div_pos (by norm_num) Real.pi_pos), hh]
  simpa only [mul_comm Complex.I] using
    mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm
      (∫ θ in 0..Real.pi / 2, Complex.exp (Complex.I * ((u * Real.cos θ : ℝ) : ℂ))))
      (show 0 ≤ 2 / Real.pi by positivity)

end Dubon2026
