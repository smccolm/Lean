import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv

open Complex MeasureTheory
open scoped Real Topology

theorem Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
    (U : Set ℂ) (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
    Integrable (fun z : ℂ => E' z * h z *
        ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z : ℂ, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
      2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
    2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by p2m_exact_reverting @_root_.P2MW.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.solution
