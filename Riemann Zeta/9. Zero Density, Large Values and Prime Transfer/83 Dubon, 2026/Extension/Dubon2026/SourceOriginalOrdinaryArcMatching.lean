import Dubon2026.SourceOriginalDisjointArcUniqueness
import Dubon2026.SourceOriginalGridCellFamilies

/-! DUB-17/18 -> original Abel-Jacobi -> geometric pairing of actual cells.
A nonempty connected original-place set mapping onto one planar side is
exactly one ordinary-sheet boundary arc. Actual finite carrier coverage,
closed disjoint carriers and the sheet coordinate formula discharge all
selection and injectivity assumptions.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalOrdinaryRegionFamily
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : RadialRegion} (B : OriginalOrdinaryRegionFamily N R)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_unique_arc_over (k : Fin R.N) {L : Set (Place ℂ F)}
    (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.arcSet k)
    (honto : R.arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L) :
    ∃! a : Σ i, Fin (B.C i).R.N, L = (B.C a.1).arc a.2 := by
  have hcov : L ⊆ ⋃ i, (B.C i).carrier := by
    intro P hP
    obtain ⟨i, hi⟩ := (B.coverage P).mp ⟨(hover P hP).1, R.arcSet_subset_K k (hover P hP).2⟩
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hLi⟩ := ArcSelection.exists_subset_of_finite_closed hL hne
    (fun i => (B.C i).carrier_isClosed) B.disjoint hcov
  let a : Fin (B.C i).R.N := Fin.cast (congrArg RadialRegion.N (B.region_eq i).symm) k
  have ha : (B.C i).R.arcSet a = R.arcSet k := RadialRegion.arcSet_cast (B.region_eq i).symm k
  have hread (P : Place ℂ F) (hP : P ∈ (B.C i).ζ.source) :
      (B.C i).ζ P = originalPlaceEval N ℂ P (jOver N ℂ) := (B.sheets.2.1 i P hP).2
  have hsub : L ⊆ (B.C i).arc a := by
    intro P hP
    have hs := ((B.C i).mem_carrier_iff_coordinate P).mp (hLi hP)
    apply ((B.C i).mem_arc_iff_coordinate a P).mpr
    exact ⟨hs.1, by rw [ha, hread P hs.1]; exact (hover P hP).2⟩
  have hinj : InjOn (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) ((B.C i).arc a) := by
    intro P hP Q hQ hPQ
    have hp := ((B.C i).mem_arc_iff_coordinate a P).mp hP
    have hq := ((B.C i).mem_arc_iff_coordinate a Q).mp hQ
    apply (B.C i).ζ.injOn hp.1 hq.1
    rw [hread P hp.1, hread Q hq.1]
    exact hPQ
  have himage : (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' (B.C i).arc a ⊆
      (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' L := by
    rintro _ ⟨P, hP, rfl⟩
    have hp := ((B.C i).mem_arc_iff_coordinate a P).mp hP
    apply honto
    simpa only [ha, hread P hp.1] using hp.2
  have heq := ArcSelection.eq_of_image_subset_of_injOn hsub himage hinj
  refine ⟨⟨i, a⟩, heq, ?_⟩
  intro b hb
  exact eq_arc_index_of_disjoint_carriers B.C B.disjoint b ⟨i, a⟩ (hb.symm.trans heq)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalOrdinaryRegionFamily
