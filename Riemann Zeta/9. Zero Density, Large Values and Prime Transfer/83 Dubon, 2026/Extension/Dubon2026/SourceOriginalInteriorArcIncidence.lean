import Dubon2026.SourceOriginalPoweredArcIncidence

/-! DUB-17/18 -> original Abel-Jacobi -> curve intersection chains.
For an actual point in an ordinary or branch carrier over a specified base
side, choose an arc through that point with exactly the full base-side image.
No local arc-incidence premise is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : RadialRegion}
local notation "F" => modularFunctionFieldOver N ℂ

theorem OriginalOrdinaryRegionFamily.arc_through (B : OriginalOrdinaryRegionFamily N R)
    (i : Fin (SourceLevelProjective.dedekindPsi N)) (k : Fin R.N) {P : Place ℂ F}
    (hP : P ∈ (B.C i).carrier) (hv : originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.arcSet k) :
    ∃ a : Fin (B.C i).R.N, P ∈ (B.C i).arc a ∧ LiesOver ((B.C i).arc a) (R.arcSet k) := by
  let C := B.C i
  let a : Fin C.R.N := Fin.cast (congrArg RadialRegion.N (B.region_eq i).symm) k
  have he : C.R.arcSet a = R.arcSet k := RadialRegion.arcSet_cast (B.region_eq i).symm k
  have hs := (C.mem_carrier_iff_coordinate P).mp hP |>.1
  refine ⟨a, (C.mem_arc_iff_coordinate a P).mpr ⟨hs, ?_⟩, ?_⟩
  · rw [he, (B.sheets.2.1 i P hs).2]
    exact hv
  · apply LiesOver.of_image_eq
    · intro Q hQ
      exact (B.sheets.2.1 i Q ((C.mem_arc_iff_coordinate a Q).mp hQ).1).1
    · rw [← he, ← C.coordinate_arc_image a]
      exact image_congr fun Q hQ =>
        ((B.sheets.2.1 i Q ((C.mem_arc_iff_coordinate a Q).mp hQ).1).2).symm

theorem OriginalBranchRegionFamily.arc_through {b : ℂ} (B : OriginalBranchRegionFamily N b R)
    (hq : R.q = b) (v : originalPositiveFiber N (jOver N ℂ) b) (k : Fin R.N) {P : Place ℂ F}
    (hP : P ∈ (B.C v).carrier) (hv : originalPlaceEval N ℂ P (jOver N ℂ) ∈ R.arcSet k) :
    ∃ a : Fin (B.C v).R.N, P ∈ (B.C v).arc a ∧ LiesOver ((B.C v).arc a) (R.arcSet k) := by
  have hread (Q : Place ℂ F) (hQ : Q ∈ (B.C v).ζ.source) :
      originalPlaceEval N ℂ Q (jOver N ℂ) = R.q + (B.C v).ζ Q ^
        ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat := by
    rw [hq]
    exact ((B.geometry v).2.2.2 Q hQ).2
  obtain ⟨a, ha, himg⟩ := (B.C v).powered_arc_through (B.geometry v).2.2.1 k
    (fun Q => originalPlaceEval N ℂ Q (jOver N ℂ)) hread hP hv
  refine ⟨a, ha, LiesOver.of_image_eq ?_ himg⟩
  intro Q hQ
  exact ((B.geometry v).2.2.2 Q (((B.C v).mem_arc_iff_coordinate a Q).mp hQ).1).1

end
end Dubon2026.SourceFunctionField.CellGeometry
