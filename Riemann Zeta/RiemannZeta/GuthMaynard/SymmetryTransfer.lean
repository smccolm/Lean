import Mathlib.Data.Complex.Basic
import RiemannZeta.GuthMaynard.ZeroCount

open Complex

namespace RiemannZeta.GuthMaynard

/-- The Functional Symmetry Hypothesis (F-13).
    Asserts that the multiplicity of a zero at `s` is equal to the multiplicity at `1 - s`, 
    restricted to nontrivial zeros in the critical strip. -/
def FunctionalSymmetryHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ s : ℂ, 0 < s.re ∧ s.re < 1 → model.multiplicity s = model.multiplicity (1 - s)

end RiemannZeta.GuthMaynard
