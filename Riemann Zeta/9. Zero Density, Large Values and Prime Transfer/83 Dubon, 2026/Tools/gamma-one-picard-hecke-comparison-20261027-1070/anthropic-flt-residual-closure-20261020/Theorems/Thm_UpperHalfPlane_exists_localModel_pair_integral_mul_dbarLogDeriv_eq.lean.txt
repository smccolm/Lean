import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq

open Complex MeasureTheory
open scoped Real Topology

theorem UpperHalfPlane.exists_localModel_pair_integral_mul_dbarLogDeriv_eq
    (b s : ℂ) (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s) :
    ∃ d F : ℂ → ℂ, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ {z : ℂ | 0 < z.im} ∧
      (∀ z ∉ K, d z = 1) ∧
      (∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
        d =ᶠ[𝓝 τ] fun z =>
          (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z) ∧
      Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ K ∧
      (∀ z : ℂ, 0 < z.im → z ≠ b →
        (fderiv ℝ d z 1 + I * fderiv ℝ d z I) / 2 / d z = F z) ∧
      ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
        Integrable (fun z : ℂ => E' z * F z) ∧ ∫ z : ℂ, E' z * F z = π * (E s - E b) := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.solution
