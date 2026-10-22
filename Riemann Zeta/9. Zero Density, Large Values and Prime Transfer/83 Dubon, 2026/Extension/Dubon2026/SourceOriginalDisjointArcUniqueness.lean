import Dubon2026.SourceOriginalCellArcGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> actual arc pairing.
Disjoint carriers and the already proved radial arc-index injectivity give
uniqueness of any arc matching a nonempty lifted set within one region family.
This single argument serves the ordinary, branch and pole families.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem RadialRegion.arcSet_cast {R R' : RadialRegion} (h : R = R') (k : Fin R.N) :
    R'.arcSet (Fin.cast (congrArg RadialRegion.N h) k) = R.arcSet k := by
  cases h
  rfl

theorem eq_arc_index_of_disjoint_carriers {ι : Type*} (C : ι → Cell N)
    (hd : Pairwise fun i j => Disjoint (C i).carrier (C j).carrier)
    (a b : Σ i, Fin (C i).R.N) (h : (C a.1).arc a.2 = (C b.1).arc b.2) : a = b := by
  obtain ⟨i, k⟩ := a
  obtain ⟨j, l⟩ := b
  have hij : i = j := by
    by_contra hne
    obtain ⟨P, hP⟩ := (C i).arc_nonempty k
    exact Set.disjoint_left.mp (hd hne) ((C i).arc_subset_carrier k hP)
      ((C j).arc_subset_carrier l (h ▸ hP))
  subst j
  have hkl : k = l := (C i).arc_index_injective h
  subst l
  rfl

end
end Dubon2026.SourceFunctionField.CellGeometry
