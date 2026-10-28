import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty

open UpperHalfPlane Complex Filter MeasureTheory Set
open scoped Topology

theorem UpperHalfPlane.integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty
    (ω : ℍ → ℂ) (Y : ℝ) (hY : 0 ≤ Y)
    (hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ)
    (hcusp : Tendsto ω atImInfty (𝓝 0))
    (hhol : ∀ τ : ℍ, Y < τ.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = g z)
    (p ρ : ℝ → ℝ) (hp : Function.support p ⊆ Ioo (-1) 1)
    (hp1 : ∀ x ∈ Icc (0 : ℝ) 1, p (x - 1) + p x = 1)
    (hρ : Function.support ρ ⊆ Ioi Y)
    (hint : Integrable fun z : ℂ => ω (ofComplex z) * (p z.re * ρ z.im : ℝ)) :
    ∫ z : ℂ, ω (ofComplex z) * (p z.re * ρ z.im : ℝ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_integral_mul_eq_zero_of_periodic_of_tendsto_atImInfty.solution
