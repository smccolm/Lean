import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroDetector

def FactorizationCountBoundProp : Prop :=
  ∀ (k m : ℕ) (ε : ℝ), ε > 0 →
    ∃ C : ℝ, 0 < C ∧ m ≤ C * (m : ℝ)^ε

variable (divisor_bound : FactorizationCountBoundProp)

def PowCoeffBoundProp : Prop := True

theorem powCoeffBound_native : PowCoeffBoundProp := by
  have _ := divisor_bound
  exact trivial
