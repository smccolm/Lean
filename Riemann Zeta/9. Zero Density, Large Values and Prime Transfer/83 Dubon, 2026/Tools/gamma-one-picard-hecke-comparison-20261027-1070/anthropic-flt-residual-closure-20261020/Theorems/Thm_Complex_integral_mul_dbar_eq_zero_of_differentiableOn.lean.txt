import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn

open Complex MeasureTheory

theorem Complex.integral_mul_dbar_eq_zero_of_differentiableOn
    (V : Set ℂ) (hV : IsOpen V) (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
    ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.solution
