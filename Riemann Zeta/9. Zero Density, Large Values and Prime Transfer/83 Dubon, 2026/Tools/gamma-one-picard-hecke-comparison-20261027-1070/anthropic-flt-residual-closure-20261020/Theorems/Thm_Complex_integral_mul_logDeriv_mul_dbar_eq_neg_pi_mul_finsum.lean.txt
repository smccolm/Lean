import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum

open MeasureTheory Complex
open scoped Topology Real

theorem Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum
    (U : Set ℂ) (hU : IsOpen U) (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z)
    (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.solution
