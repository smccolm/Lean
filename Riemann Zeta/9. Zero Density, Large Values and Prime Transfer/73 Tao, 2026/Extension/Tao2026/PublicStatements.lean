import Mathlib.NumberTheory.LSeries.Dirichlet
import Tao2026.Asymptotics
import Tao2026.Counting

/-!
# Frozen public statement contracts

These are exact proposition-valued contracts for Tao's Theorems 1.7--1.10.
They are definitions, not theorem claims. The eventual public proofs must have
these conclusions without additional mathematical hypotheses.
-/

namespace Tao2026

/-- The source notation `log₂ x`. -/
noncomputable def iteratedLog (x : ℕ) : ℝ := Real.log (Real.log x)

/-- Tao's saddle-point exponent `u₀`, equation `u-def`. -/
noncomputable def taoUZero (x : ℕ) : ℝ :=
  Real.sqrt 2 * Real.sqrt (Real.log x) / Real.sqrt (iteratedLog x)

/-- Tao's smoothness threshold `z`, equation `z-def`. -/
noncomputable def taoZ (x : ℕ) : ℝ :=
  Real.exp ((1 / Real.sqrt 2) * Real.sqrt (Real.log x) *
    Real.sqrt (iteratedLog x))

/-- The real constant `ζ(3/2)/ζ(3)` occurring in Theorem 1.8. -/
noncomputable def powerfulNumberConstant : ℝ :=
  (riemannZeta (3 / 2 : ℝ)).re / (riemannZeta (3 : ℝ)).re

/-- Exact conclusion contract for Tao Theorem 1.7. -/
def TaoTheorem17Conclusion : Prop :=
  LogPowerSavingRelative
      (fun x => (nontrivialBadCount x : ℝ))
      (fun x => (badOneTermCount x : ℝ)) ∧
    QuotientPowerScale
      (fun x => (badCount x : ℝ))
      (fun x => (x : ℝ)) taoZ 2

/-- Exact conclusion contract for Tao Theorem 1.8. -/
def TaoTheorem18Conclusion : Prop :=
  PowerUpperBound (fun x => (nontrivialVeryBadCount x : ℝ)) (2 / 5) ∧
    SequenceEquivalent
      (fun x => (veryBadCount x : ℝ))
      (fun x => powerfulNumberConstant * Real.sqrt x)

/-- Exact conclusion contract for Tao Theorem 1.9. -/
def TaoTheorem19Conclusion : Prop :=
  PowerUpperBound
      (fun x => (nontrivialFactorialThreeCount x : ℝ)) (1 / 2) ∧
    PowerScale (fun x => (factorialThreeCount x : ℝ)) (1 / 2)

/-- Exact conclusion contract for Tao Theorem 1.10. -/
def TaoTheorem110Conclusion : Prop :=
  PowerScale (fun x => (factorialSquareTripleCount x : ℝ)) (1 / 2)

end Tao2026
