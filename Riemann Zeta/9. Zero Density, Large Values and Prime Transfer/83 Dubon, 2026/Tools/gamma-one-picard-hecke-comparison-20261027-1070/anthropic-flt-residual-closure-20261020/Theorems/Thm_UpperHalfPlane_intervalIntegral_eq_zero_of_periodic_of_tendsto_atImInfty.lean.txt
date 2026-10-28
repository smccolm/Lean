import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty

open UpperHalfPlane Complex Filter
open scoped Topology

theorem UpperHalfPlane.intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (y : ℝ) (hy : Y < y) :
    ∫ x in (0 : ℝ)..1, ω (ofComplex (x + y * Complex.I)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty.solution
