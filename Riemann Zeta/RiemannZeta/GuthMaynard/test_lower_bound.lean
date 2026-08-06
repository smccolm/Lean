import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Instances.Complex

open Complex

namespace RiemannZeta.GuthMaynard

variable (zeta_lower_bound : ∃ (c_0 : ℝ), c_0 > 0 ∧
    ∀ (t : ℝ), t ≥ 1 →
      c_0 ≤ ‖riemannZeta (2 + I * (t + 1/2))‖)

end RiemannZeta.GuthMaynard
