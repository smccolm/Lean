import Dubon2026.SourceOriginalPoweredArcMatching
import Dubon2026.SourceOriginalGridCellFamilies

/-! DUB-17/18 -> original Abel-Jacobi -> actual branch-cell arc matching.
The constructed branch family covers the full original j preimage of its
base region. Finite closed separation chooses one actual carrier, then the
exact power geometry identifies its unique complete boundary arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalBranchRegionFamily
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : RadialRegion} {b : ℂ}
    (B : OriginalBranchRegionFamily N b R)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_unique_arc_over (hq : R.q = b) (k : Fin R.N) {L : Set (Place ℂ F)}
    (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.arcSet k)
    (honto : R.arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L) :
    ∃! a : Σ v, Fin (B.C v).R.N, L = (B.C a.1).arc a.2 := by
  have hcov : L ⊆ ⋃ v, (B.C v).carrier := by
    intro P hP
    obtain ⟨v, hv⟩ := (B.coverage P).mp ⟨(hover P hP).1, R.arcSet_subset_K k (hover P hP).2⟩
    exact mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨v, hLv⟩ := ArcSelection.exists_subset_of_finite_closed hL hne
    (fun v => (B.C v).carrier_isClosed) B.disjoint hcov
  have hread (P : Place ℂ F) (hP : P ∈ (B.C v).ζ.source) :
      originalPlaceEval N ℂ P (jOver N ℂ) = R.q + (B.C v).ζ P ^
        ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat := by
    rw [hq]
    exact ((B.geometry v).2.2.2 P hP).2
  obtain ⟨a, ha, _, _⟩ := (B.C v).exists_powered_arc_over (B.geometry v).2.2.1 k
    (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) hread hL hne hLv
    (fun P hP => (hover P hP).2) honto
  refine ⟨⟨v, a⟩, ha, ?_⟩
  intro a' ha'
  exact eq_arc_index_of_disjoint_carriers B.C B.disjoint a' ⟨v, a⟩ (ha'.symm.trans ha)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalBranchRegionFamily
