import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Relation
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> 2g generating loops -> tree/cotree.
Integer chains retain the actual edge labels needed by period sums. The source
minimal connected subset argument avoids translating a multigraph into a simple
graph and back. These foundations will be consumed by the original dissection
tree/cotree theorem; no loop generation is claimed at this intermediate stage.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (hd tl : E → V)

/-- Integer boundary on the exact oriented edge index, retaining loops and repeated edges. -/
def bd (c : E → ℤ) (w : V) : ℤ :=
  (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e)

omit [Fintype V] [DecidableEq E] in
theorem bd_add (c d : E → ℤ) (w : V) :
    bd hd tl (c + d) w = bd hd tl c w + bd hd tl d w := by
  unfold bd; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring

omit [Fintype V] [DecidableEq E] in
theorem bd_sub (c d : E → ℤ) (w : V) :
    bd hd tl (c - d) w = bd hd tl c w - bd hd tl d w := by
  unfold bd; simp only [Pi.sub_apply, Finset.sum_sub_distrib]; ring

omit [Fintype V] in
theorem bd_single (e₀ : E) (w : V) :
    bd hd tl (fun e => if e = e₀ then (1 : ℤ) else 0) w =
      (if w = hd e₀ then 1 else 0) - (if w = tl e₀ then 1 else 0) := by
  unfold bd
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, eq_comm (a := w)]

omit [Fintype V] [DecidableEq E] in
theorem bd_smul (n : ℤ) (c : E → ℤ) (w : V) :
    bd hd tl (n • c) w = n * bd hd tl c w := by
  unfold bd; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

omit [Fintype V] [DecidableEq E] in
theorem bd_finsum {ι : Type*} (s : Finset ι) (f : ι → E → ℤ) (w : V) :
    bd hd tl (fun e => ∑ i ∈ s, f i e) w = ∑ i ∈ s, bd hd tl (f i) w := by
  unfold bd
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (t := s), Finset.sum_comm (t := s)]

/-- Every ordered pair is joined by an integer chain supported on the chosen edges. -/
def IsConn (S : Finset E) : Prop :=
  ∀ u v : V, ∃ c : E → ℤ, (∀ e ∉ S, c e = 0) ∧ ∀ w, bd hd tl c w =
    (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)

/-- Each ordered pair has a unique integer chain on the chosen edges. -/
def IsTree (T : Finset E) : Prop :=
  ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧ ∀ w, bd hd tl c w =
    (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)

/-- Undirected adjacency witnessed by an actual chosen edge. -/
def adj (S : Finset E) : V → V → Prop :=
  fun a b => ∃ e ∈ S, (hd e = a ∧ tl e = b) ∨ (hd e = b ∧ tl e = a)

/-- Reachability using the actual chosen edges. -/
abbrev IsWalkConn (S : Finset E) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (adj hd tl S) u v

end
end Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
