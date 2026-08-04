import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set Metric

namespace RiemannZeta.GuthMaynard

/-- A finite set `W` of real numbers is `δ`-separated if the distance between any two distinct points is at least `δ`. -/
def IsSeparated (δ : ℝ) (W : Finset ℝ) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → δ ≤ dist x y

/-- 
The exact interval used in the zero-density theorem (Section 13.1) dyadic decomposition:
points lie in `[T, 2 * T]`.
-/
def InTargetInterval (T : ℝ) (W : Finset ℝ) : Prop :=
  ∀ (x : ℝ), x ∈ W → x ∈ Icc T (2 * T)

/-- The interval for the basic Large Values Estimate (Theorem 1.1) is `[0, T]`. -/
def InBaseInterval (T : ℝ) (W : Finset ℝ) : Prop :=
  ∀ (x : ℝ), x ∈ W → x ∈ Icc 0 T

/-- 
Translation of a finite set by a constant `c`. 
This is used in Phase 4 to map `[T, 2T]` to `[0, T]`.
-/
noncomputable def translateSet (c : ℝ) (W : Finset ℝ) : Finset ℝ :=
  W.image (fun x => x - c)

theorem isSeparated_translate (δ c : ℝ) (W : Finset ℝ) (h : IsSeparated δ W) : 
    IsSeparated δ (translateSet c W) := by
  intro x hx y hy hxy
  rw [translateSet, Finset.mem_image] at hx hy
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  have hx'y' : x' ≠ y' := by
    intro hc
    rw [hc] at hxy
    exact hxy rfl
  have hd : dist (x' - c) (y' - c) = dist x' y' := by
    dsimp [dist]
    congr 1
    ring
  rw [hd]
  exact h x' hx' y' hy' hx'y'

theorem inBaseInterval_translate (T : ℝ) (W : Finset ℝ) (h : InTargetInterval T W) :
    InBaseInterval T (translateSet T W) := by
  intro x hx
  rw [translateSet, Finset.mem_image] at hx
  rcases hx with ⟨x', hx', rfl⟩
  have hT := h x' hx'
  rw [mem_Icc] at hT ⊢
  constructor
  · linarith [hT.1]
  · linarith [hT.2]

end RiemannZeta.GuthMaynard

/-- 
Combinatorial separation extraction hypothesis. 
States that from any finite set S where local occupancy in [x, x+1) is bounded by L,
we can extract a 1-separated subset W whose size is proportional to S.
Isolated as a hypothesis pending a full Lean combinatorial proof.
-/
def SeparatedSelectionHypothesis : Prop :=
  ∀ (S : Finset ℝ) (L : ℕ),
    (∀ (x : ℤ), (S.filter (fun t => (x : ℝ) ≤ t ∧ t < (x : ℝ) + 1)).card ≤ L) →
    ∃ W ⊆ S, RiemannZeta.GuthMaynard.IsSeparated 1 W ∧ S.card ≤ 2 * L * W.card
