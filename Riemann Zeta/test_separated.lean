import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor

open Set Metric

def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ dist x y

theorem exists_oneSeparated_subset (S : Finset ℝ) (L : ℕ)
    (hlocal : ∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ L) :
    ∃ W ⊆ S, IsSeparated 1 W ∧ S.card ≤ 2 * L * W.card := by
  sorry
