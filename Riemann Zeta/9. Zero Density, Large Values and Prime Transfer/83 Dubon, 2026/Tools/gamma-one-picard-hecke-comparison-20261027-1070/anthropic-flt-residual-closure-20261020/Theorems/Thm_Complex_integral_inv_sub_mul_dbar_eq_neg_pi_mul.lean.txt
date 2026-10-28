import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul

open Complex MeasureTheory
open scoped Real

theorem Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul
    (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.solution
