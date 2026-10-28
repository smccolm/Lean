import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue

open Complex MeasureTheory
open scoped Topology Real

theorem Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.solution
