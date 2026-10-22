import Dubon2026.SourceOriginalGlobalCellPairing

/-! DUB-17/18 -> original Abel-Jacobi -> curve intersection chains.
At a fixed original place, a planar region determines its actual cell.
Reuse disjoint carriers within each constructed family. This also handles
poles directly, avoiding a separate identification of the pole with a center.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace

theorem eq_of_mem_disjoint_family {X ι : Type*} {C : ι → Set X}
    (hd : Pairwise fun i j => Disjoint (C i) (C j)) {i j : ι} {P : X}
    (hi : P ∈ C i) (hj : P ∈ C j) : i = j := by
  by_contra hne
  exact Set.disjoint_left.mp (hd hne) hi hj

namespace OriginalGlobalCellCover
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem cell_eq_of_common_place (i j : A.Index) {P : Place ℂ (modularFunctionFieldOver N ℂ)}
    (hi : P ∈ (A.cell i).carrier) (hj : P ∈ (A.cell j).carrier)
    (hr : A.regionOf i = A.regionOf j) : i = j := by
  rcases i with (⟨p, i⟩ | ⟨v, i⟩) | i <;>
    rcases j with (⟨q, j⟩ | ⟨w, j⟩) | j
  · have hpq : p = q := Subtype.ext (Subtype.ext (Option.some.inj hr))
    subst q
    have he := eq_of_mem_disjoint_family (A.G.ordinary p.1 p.2).disjoint hi hj
    exact congrArg (fun a => (Sum.inl (Sum.inl (p, a)) : A.Index)) he
  · have h := A.G.branch_cap w
    rw [← Option.some.inj hr] at h
    have hf := p.2.symm.trans h
    cases hf
  · cases hr
  · have h := A.G.branch_cap v
    rw [Option.some.inj hr] at h
    have hf := q.2.symm.trans h
    cases hf
  · have hvw : v = w := by
      apply Subtype.ext
      apply Option.some.inj
      exact (A.G.branch_cap v).symm.trans
        ((congrArg A.G.D.capAt (Option.some.inj hr)).trans (A.G.branch_cap w))
    subst w
    have he := eq_of_mem_disjoint_family
      (A.G.branch (A.G.branchSquare v) v (A.G.branch_cap v)).disjoint hi hj
    exact congrArg (fun a => (Sum.inl (Sum.inr ⟨v, a⟩) : A.Index)) he
  · cases hr
  · cases hr
  · cases hr
  · have he := eq_of_mem_disjoint_family A.poles.disjoint hi hj
    exact congrArg (fun a => (Sum.inr a : A.Index)) he

end OriginalGlobalCellCover
end
end Dubon2026.SourceFunctionField.CellGeometry
