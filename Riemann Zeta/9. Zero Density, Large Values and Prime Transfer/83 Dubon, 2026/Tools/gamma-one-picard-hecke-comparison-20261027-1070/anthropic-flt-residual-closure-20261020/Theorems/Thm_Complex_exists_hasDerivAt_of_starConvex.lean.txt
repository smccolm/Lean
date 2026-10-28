import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_exists_hasDerivAt_of_starConvex

theorem Complex.exists_hasDerivAt_of_starConvex {U : Set ℂ} (hU : IsOpen U) {q : ℂ} (hq : q ∈ U)
    (hstar : StarConvex ℝ q U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ g : ℂ → ℂ, g q = 0 ∧ ∀ z ∈ U, HasDerivAt g (f z) z := by p2m_exact_reverting @_root_.P2MW.S_Complex_exists_hasDerivAt_of_starConvex.solution
