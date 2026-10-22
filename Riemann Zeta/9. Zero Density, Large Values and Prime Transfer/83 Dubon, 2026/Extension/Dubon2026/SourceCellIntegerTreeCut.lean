import Dubon2026.SourceCellIntegerTreeCardinality

/-! DUB-17/18 -> raw reciprocity -> polygon-word gluing.
A nontrivial partition of a connected integer tree has a crossing edge.
This selects the next actual cotree edge in the finite cell-gluing induction.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (hd tl : E → V)

omit [Fintype V] in
theorem exists_crossing {T : Finset E} (hT : IsTree hd tl T) {A : Finset V} {u v : V}
    (hu : u ∈ A) (hv : v ∉ A) : ∃ e ∈ T, ¬ (hd e ∈ A ↔ tl e ∈ A) := by
  classical
  obtain ⟨c, ⟨hcT, hcbd⟩, -⟩ := hT u v
  by_contra hall
  push Not at hall
  have hsum : ∑ w ∈ A, bd hd tl c w = -1 := by
    rw [Finset.sum_congr rfl (fun w _ => hcbd w), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' A v, Finset.sum_ite_eq' A u, if_neg hv, if_pos hu]
    ring
  rw [sum_bd_eq] at hsum
  have hzero : ∀ e ∈ (Finset.univ : Finset E),
      ((if hd e ∈ A then c e else 0) - (if tl e ∈ A then c e else 0)) = 0 := by
    intro e _
    by_cases heT : e ∈ T
    · have hiff := hall e heT
      by_cases hh : hd e ∈ A
      · rw [if_pos hh, if_pos (hiff.1 hh), sub_self]
      · rw [if_neg hh, if_neg (fun h => hh (hiff.2 h)), sub_self]
    · rw [hcT e heT]; simp
  rw [Finset.sum_eq_zero hzero] at hsum
  exact absurd hsum (by norm_num)

end
end Dubon2026.SourceFunctionField.CellGeometry.IntegerEdgeChains
