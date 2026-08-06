import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex

open Complex

namespace RiemannZeta.GuthMaynard

-- We want to prove that riemannZeta is bounded below on Re(s) = 2.
-- For now, let's just see if we can state it as a lemma and admit it.
lemma zeta_lower_bound : ∃ (c_0 : ℝ), c_0 > 0 ∧
    ∀ (T t : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
      c_0 ≤ ‖riemannZeta (2 + I * (t + 1/2))‖ := by
  sorry

end RiemannZeta.GuthMaynard
