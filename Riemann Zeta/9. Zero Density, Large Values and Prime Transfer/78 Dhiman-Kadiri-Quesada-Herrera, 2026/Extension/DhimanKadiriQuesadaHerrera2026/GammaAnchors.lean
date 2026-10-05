import DhimanKadiriQuesadaHerrera2026.GammaHorizontal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Exact Gamma norms at the endpoints of the horizontal segment

Both anchors follow from Gamma reflection and conjugation. The exponential
majorants are ordinary real inequalities, without an asymptotic remainder premise.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped ComplexConjugate

/-- The half-line Gamma norm is the exact hyperbolic-cosine expression. -/
theorem norm_Gamma_half_add_imag_sq (t : ℝ) :
    ‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  have hc : 1 - ((1 / 2 : ℂ) + (t : ℂ) * I) =
      conj ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  have hs : sin ((Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) =
      (Real.pi : ℂ) / 2 + ((Real.pi * t : ℝ) : ℂ) * I by push_cast; ring,
      sin_add, sin_pi_div_two, cos_pi_div_two, one_mul, zero_mul, add_zero,
      cos_mul_I, ← ofReal_cosh]
  have h := congrArg norm (Gamma_mul_Gamma_one_sub ((1 / 2 : ℂ) + (t : ℂ) * I))
  simpa only [hc, Gamma_conj, norm_mul, norm_conj, hs, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos (Real.cosh_pos _), pow_two] using h

/-- The purely imaginary Gamma norm is the exact hyperbolic-sine expression. -/
theorem norm_Gamma_imag_sq {t : ℝ} (ht : 0 < t) :
    ‖Gamma ((t : ℂ) * I)‖ ^ 2 = Real.pi / (t * Real.sinh (Real.pi * t)) := by
  have hz : -(t : ℂ) * I ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (ofReal_ne_zero.mpr ht.ne')) I_ne_zero
  have hg : Gamma (1 - (t : ℂ) * I) =
      (-(t : ℂ) * I) * conj (Gamma ((t : ℂ) * I)) := by
    rw [show 1 - (t : ℂ) * I = -(t : ℂ) * I + 1 by ring, Gamma_add_one _ hz]
    have hc : -(t : ℂ) * I = conj ((t : ℂ) * I) := by simp
    rw [hc, Gamma_conj]
  have hs : sin ((Real.pi : ℂ) * ((t : ℂ) * I)) =
      (Real.sinh (Real.pi * t) : ℂ) * I := by
    rw [show (Real.pi : ℂ) * ((t : ℂ) * I) = ((Real.pi * t : ℝ) : ℂ) * I by
      push_cast; ring, sin_mul_I, ← ofReal_sinh]
  have hp : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  have h := congrArg norm (Gamma_mul_Gamma_one_sub ((t : ℂ) * I))
  simp only [hg, hs, norm_mul, norm_neg, norm_I, mul_one, norm_conj, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, abs_of_pos hp,
    abs_of_pos Real.pi_pos] at h
  apply (eq_div_iff (mul_ne_zero ht.ne' hp.ne')).mpr
  have hh := (eq_div_iff hp.ne').mp h
  nlinarith [hh]

/-- The half-line anchor has the sharp elementary exponential majorant. -/
theorem norm_Gamma_half_add_imag_sq_le (t : ℝ) :
    ‖Gamma ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-Real.pi * t) := by
  rw [norm_Gamma_half_add_imag_sq]
  have hc : Real.exp (Real.pi * t) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(Real.pi * t))]
  calc
    _ ≤ Real.pi / (Real.exp (Real.pi * t) / 2) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) hc
    _ = _ := by
      rw [show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
      ring

/-- A quadratic exponential bound gives a uniform rational majorant for the small tail. -/
theorem exp_neg_two_pi_mul_le {t : ℝ} (ht : 0 < t) :
    Real.exp (-2 * Real.pi * t) ≤ 1 / (12 * t) := by
  have hp : 6 * t ≤ 2 * Real.pi * t := by nlinarith [Real.pi_gt_three]
  have hquad := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * Real.pi * t by positivity)
  have hs : (6 * t) ^ 2 ≤ (2 * Real.pi * t) ^ 2 := by nlinarith
  have hlow : 12 * t ≤ Real.exp (2 * Real.pi * t) := by
    nlinarith [sq_nonneg (6 * t - 1)]
  rw [show -2 * Real.pi * t = -(2 * Real.pi * t) by ring, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hlow

/-- At the source threshold, the geometric tail is at most one half. -/
theorem exp_neg_two_pi_mul_le_half {t : ℝ} (ht : 1 / Real.pi ≤ t) :
    Real.exp (-2 * Real.pi * t) ≤ 1 / 2 := by
  have hpi : 1 ≤ Real.pi * t := by
    simpa only [mul_comm] using (div_le_iff₀ Real.pi_pos).mp ht
  have hlow := Real.add_one_le_exp (2 * Real.pi * t)
  have he : 2 ≤ Real.exp (2 * Real.pi * t) := by linarith
  rw [show -2 * Real.pi * t = -(2 * Real.pi * t) by ring, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) he

/-- The elementary geometric denominator is bounded by an exponential on the full interval. -/
theorem one_div_one_sub_le_exp {r : ℝ} (hr : r ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    1 / (1 - r) ≤ Real.exp (2 * r) := by
  have hd : 0 < 1 - r := by linarith [hr.2]
  rw [div_le_iff₀ hd]
  have hm := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * r)) hd.le
  nlinarith [hr.1, hr.2]

/-- The geometric correction of the imaginary Gamma anchor is controlled at the source threshold. -/
theorem gamma_imag_geometric_correction_le {t : ℝ} (ht : 1 / Real.pi ≤ t) :
    1 / (1 - Real.exp (-2 * Real.pi * t)) ≤ Real.exp (1 / (6 * t)) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  have hr := exp_neg_two_pi_mul_le htpos
  refine (one_div_one_sub_le_exp ⟨(Real.exp_pos _).le, exp_neg_two_pi_mul_le_half ht⟩).trans ?_
  apply Real.exp_le_exp.mpr
  have he : 2 * (1 / (12 * t)) = 1 / (6 * t) := by ring
  linarith

/-- The imaginary-axis Gamma norm has its exact positive exponential/geometric form. -/
theorem norm_Gamma_imag_sq_eq_geometric {t : ℝ} (ht : 0 < t) :
    ‖Gamma ((t : ℂ) * I)‖ ^ 2 =
      (2 * Real.pi / t) * Real.exp (-Real.pi * t) *
        (1 / (1 - Real.exp (-2 * Real.pi * t))) := by
  have hm : Real.exp (Real.pi * t) * Real.exp (-2 * Real.pi * t) =
      Real.exp (-Real.pi * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.sinh (Real.pi * t) =
      Real.exp (Real.pi * t) * (1 - Real.exp (-2 * Real.pi * t)) / 2 := by
    rw [Real.sinh_eq, show -(Real.pi * t) = -Real.pi * t by ring]
    linear_combination hm / 2
  rw [norm_Gamma_imag_sq ht, hs, show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The imaginary-axis anchor is controlled by the explicit leading Stirling-size factor. -/
theorem norm_Gamma_imag_sq_le {t : ℝ} (ht : 1 / Real.pi ≤ t) :
    ‖Gamma ((t : ℂ) * I)‖ ^ 2 ≤
      (2 * Real.pi / t) * Real.exp (-Real.pi * t) * Real.exp (1 / (6 * t)) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht
  rw [norm_Gamma_imag_sq_eq_geometric htpos]
  exact mul_le_mul_of_nonneg_left (gamma_imag_geometric_correction_le ht) (by positivity)

end DhimanKadiriQuesadaHerrera2026
