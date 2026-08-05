import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.BetaDependence

open Complex
open Finset

namespace RiemannZeta.GuthMaynard

/--
The classical local zero-density estimate:
The number of zeros in a unit interval [t, t+1] is bounded by O(log T)
for t ∈ [T, 2T].
-/
def LocalZeroCountHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∃ C > 0, ∀ (σ t T : ℝ), T ≥ 2 → t ∈ Set.Icc T (2 * T) →
    (zeroCountRect model σ 1 t (t + 1) : ℝ) ≤ C * Real.log T

/-- Number of Type I zeros in the rectangle counting analytical multiplicity. -/
noncomputable def typeIZeroCount (model : ZetaZeroCountModel) (σ T1 T2 T : ℝ) : ℕ :=
  ∑ s ∈ (zerosInRect model σ 1 T1 T2).filter (fun ρ => IsTypeIZero ρ T), model.multiplicity s

/--
F-05: Extract separated ordinates for Type I zeros.
For any `T ≥ 2` and `σ`, and after beta removal, we can extract a 1-separated set 
`W ⊂ [T, 2T]` tied to a *single* fixed dyadic `N`.
The fixed-line detector is large on `W` and the size of `W` controls the 
total Type I zero count up to logs and epsilons.
-/
def ExtractSeparatedHypothesis (model : ZetaZeroCountModel) : Prop :=
  ∀ (σ T ε : ℝ), T ≥ 2 → ε > 0 →
    ∃ (W : Finset ℝ) (N : ℕ) (C : ℝ), 
      C > 0 ∧
      (T ^ (1/100 : ℝ) ≤ N ∧ N ≤ T ^ (1/2 : ℝ) * (Real.log T) ^ 2) ∧
      IsSeparated 1 W ∧ InTargetInterval T W ∧
      (∀ γ' ∈ W, 1 / (4 * Real.log T) ≤ ‖detectPoly N (σ + I * γ') T‖) ∧
      ((typeIZeroCount model σ T (2 * T) T : ℝ) ≤ C * T^ε * (W.card : ℝ) * Real.log T)

end RiemannZeta.GuthMaynard
