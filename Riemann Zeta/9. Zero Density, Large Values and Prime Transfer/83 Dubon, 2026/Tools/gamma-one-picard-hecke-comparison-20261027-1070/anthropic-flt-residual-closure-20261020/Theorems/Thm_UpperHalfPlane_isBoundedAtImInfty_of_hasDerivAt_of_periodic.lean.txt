import Mathlib
import P2M.Util
import P2M.Sol.S_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic

set_option autoImplicit false

open scoped Manifold

theorem UpperHalfPlane.isBoundedAtImInfty_of_hasDerivAt_of_periodic {h : ℝ} (hh : 0 < h) {u v : UpperHalfPlane → ℂ}
    (hu_per : Function.Periodic (u ∘ UpperHalfPlane.ofComplex) h) (hu_hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u)
    (hu_bdd : UpperHalfPlane.IsBoundedAtImInfty u)
    (hv : ∀ τ : UpperHalfPlane, HasDerivAt (v ∘ UpperHalfPlane.ofComplex) (u τ) ↑τ)
    (hv_per : Function.Periodic (v ∘ UpperHalfPlane.ofComplex) h) :
    UpperHalfPlane.IsBoundedAtImInfty v := by p2m_exact_reverting @_root_.P2MW.S_UpperHalfPlane_isBoundedAtImInfty_of_hasDerivAt_of_periodic.solution
