import Mathlib.Data.Complex.Basic
import RiemannZeta.GuthMaynard.ZeroCount

open Complex

namespace RiemannZeta.GuthMaynard

/-- The Functional Symmetry Hypothesis (F-13).
    Asserts that the multiplicity of a zero at `s` is equal to the multiplicity at `1 - s`. -/
def FunctionalSymmetryHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ s : ℂ, model.multiplicity s = model.multiplicity (1 - s)

end RiemannZeta.GuthMaynard
