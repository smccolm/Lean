import Dubon2026.SourceOriginalGlobalArcSides

/-! DUB-17/18 -> original Abel-Jacobi -> the global pairing involution.
Within one planar region, equality of actual arc sets determines the global
cell and arc index. Reuse the proved disjoint-carrier theorem for each family.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem arc_region_ext (a b : A.Arc) (hr : A.regionOf a.1 = A.regionOf b.1)
    (ha : A.arcPlaces a = A.arcPlaces b) : a = b := by
  rcases a with ⟨i, k⟩
  rcases b with ⟨j, l⟩
  rcases i with (⟨p, i⟩ | ⟨v, i⟩) | i <;>
    rcases j with (⟨q, j⟩ | ⟨w, j⟩) | j
  · have hpq : p = q := Subtype.ext (Subtype.ext (Option.some.inj hr))
    subst q
    have he := eq_arc_index_of_disjoint_carriers (A.G.ordinary p.1 p.2).C
      (A.G.ordinary p.1 p.2).disjoint ⟨i, k⟩ ⟨j, l⟩ ha
    exact congrArg (fun a => (⟨.inl (.inl (p, a.1)), a.2⟩ : A.Arc)) he
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
    have he := eq_arc_index_of_disjoint_carriers
      (A.G.branch (A.G.branchSquare v) v (A.G.branch_cap v)).C
      (A.G.branch (A.G.branchSquare v) v (A.G.branch_cap v)).disjoint ⟨i, k⟩ ⟨j, l⟩ ha
    exact congrArg (fun a => (⟨.inl (.inr ⟨v, a.1⟩), a.2⟩ : A.Arc)) he
  · cases hr
  · cases hr
  · cases hr
  · have he := eq_arc_index_of_disjoint_carriers A.poles.C A.poles.disjoint ⟨i, k⟩ ⟨j, l⟩ ha
    exact congrArg (fun a => (⟨.inr a.1, a.2⟩ : A.Arc)) he

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
