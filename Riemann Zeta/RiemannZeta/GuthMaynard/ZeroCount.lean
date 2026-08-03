import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Data.Real.Basic

open Complex

namespace RiemannZeta.GuthMaynard

/-- A precise rectangle in the complex plane: σ_min ≤ Re(s) ≤ σ_max, T_min ≤ Im(s) ≤ T_max -/
def ZeroRectangle (σ_min σ_max T_min T_max : ℝ) : Set ℂ :=
  { s : ℂ | σ_min ≤ s.re ∧ s.re ≤ σ_max ∧ T_min ≤ s.im ∧ s.im ≤ T_max }

/-- An interface for counting zeros of the Riemann Zeta function with multiplicity. -/
structure ZetaZeroCountModel where
  multiplicity : ℂ → ℕ
  zero_iff : ∀ s : ℂ, multiplicity s > 0 ↔ riemannZeta s = 0
  finite_zeros : ∀ σ_min σ_max T_min T_max,
    (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite

/-- The exact finite set of zeros in a rectangle. -/
noncomputable def zerosInRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : Finset ℂ :=
  (model.finite_zeros σ_min σ_max T_min T_max).toFinset

open scoped BigOperators

/-- Number of zeros in the rectangle counting multiplicity -/
noncomputable def zeroCountRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  ∑ s ∈ zerosInRect model σ_min σ_max T_min T_max, model.multiplicity s

/-- The zero-counting function N(σ, T): number of zeros with Re(s) ≥ σ and 0 ≤ Im(s) ≤ T. -/
noncomputable def N (model : ZetaZeroCountModel) (σ T : ℝ) : ℕ :=
  zeroCountRect model σ 1 0 T

/-- The dyadic zero reduction proposition (F-01).
    This states that the global zero count N(σ, T) can be bounded by a finite sum
    of counts in dyadic intervals. -/
def DyadicReductionProp (model : ZetaZeroCountModel) (σ T : ℝ) : Prop :=
  ∃ k : ℕ, N model σ T ≤ ∑ j ∈ Finset.range k,
    zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ))

end RiemannZeta.GuthMaynard
