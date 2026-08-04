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

/-- An interface for counting zeros of the Riemann Zeta function with analytic multiplicity.
    This serves as the canonical description of the zeros used throughout the proof. -/
structure ZetaZeroCountModel where
  /-- Analytic multiplicity of a zero. -/
  multiplicity : ℂ → ℕ
  /-- A point has positive multiplicity if and only if it is a zero of riemannZeta. -/
  zero_iff : ∀ s : ℂ, multiplicity s > 0 ↔ riemannZeta s = 0
  /-- The zeros are isolated, so they are finite in any compact rectangle. -/
  finite_zeros : ∀ σ_min σ_max T_min T_max,
    (ZeroRectangle σ_min σ_max T_min T_max ∩ {s | riemannZeta s = 0}).Finite

open scoped BigOperators

/-- The exact finite set of distinct zeros in a bounded rectangle.
    This connects the analytical zeros to finite collections used in combinatorial extraction arguments. -/
noncomputable def zerosInRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : Finset ℂ :=
  (model.finite_zeros σ_min σ_max T_min T_max).toFinset

/-- Cardinality of the set of distinct zeros in the rectangle. -/
noncomputable def distinctZeroCountRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  (zerosInRect model σ_min σ_max T_min T_max).card

/-- Number of zeros in the rectangle counting analytical multiplicity. -/
noncomputable def zeroCountRect (model : ZetaZeroCountModel) (σ_min σ_max T_min T_max : ℝ) : ℕ :=
  ∑ s ∈ zerosInRect model σ_min σ_max T_min T_max, model.multiplicity s

/-- The classical zero-counting function N(σ, T): number of zeros (with multiplicity)
    with Re(s) ≥ σ and 0 ≤ Im(s) ≤ T. -/
noncomputable def N (model : ZetaZeroCountModel) (σ T : ℝ) : ℕ :=
  zeroCountRect model σ 1 0 T

/-- The dyadic zero reduction proposition.
    This states that the global zero count N(σ, T) can be bounded by a finite sum
    of counts in dyadic intervals. -/
def DyadicReductionProp (model : ZetaZeroCountModel) (σ T : ℝ) : Prop :=
  ∃ k : ℕ, N model σ T ≤ ∑ j ∈ Finset.range k,
    zeroCountRect model σ 1 (T / 2^((j:ℝ)+1)) (T / 2^(j:ℝ))

end RiemannZeta.GuthMaynard
