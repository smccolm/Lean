import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_trivialization_add_pow

theorem Complex.exists_trivialization_add_pow {b : ℂ} {θ : ℝ} {e : ℕ} (he : e ≠ 0) {U : Set ℂ}
    (hray : ∀ z ∈ U, ∀ t : ℝ, 0 ≤ t → b + t * Complex.exp (θ * Complex.I) ≠ z) :
    ∃ H : ((fun ζ : ℂ => b + ζ ^ e) ⁻¹' U) ≃ₜ U × Fin e,
      ∀ ζ, ((H ζ).1 : ℂ) = b + (ζ : ℂ) ^ e := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_trivialization_add_pow.solution
