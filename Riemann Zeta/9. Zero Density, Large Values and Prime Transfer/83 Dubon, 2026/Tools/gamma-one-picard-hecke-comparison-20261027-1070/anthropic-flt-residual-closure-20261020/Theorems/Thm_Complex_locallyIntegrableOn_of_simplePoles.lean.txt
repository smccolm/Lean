import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_locallyIntegrableOn_of_simplePoles

open Complex MeasureTheory
open scoped Topology

theorem Complex.locallyIntegrableOn_of_simplePoles
    (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U := by p2m_exact_reverting @_root_.P2MW.S_Complex_locallyIntegrableOn_of_simplePoles.solution
