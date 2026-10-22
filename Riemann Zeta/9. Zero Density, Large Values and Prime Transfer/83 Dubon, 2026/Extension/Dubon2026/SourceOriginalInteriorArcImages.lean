import Dubon2026.SourceOriginalPoweredArcImage
import Dubon2026.SourceOriginalGlobalArcMatching

/-! DUB-17/18 -> original Abel-Jacobi -> actual boundary partners.
Ordinary and branch arcs have regular j values and map injectively onto a
single full base side. Thus the unique matching theorem applies to the
opposite planar region without an added side-image or injectivity premise.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {R : RadialRegion}
local notation "F" => modularFunctionFieldOver N ℂ

theorem OriginalOrdinaryRegionFamily.arc_image (B : OriginalOrdinaryRegionFamily N R)
    (i : Fin (SourceLevelProjective.dedekindPsi N)) (a : Fin (B.C i).R.N) :
    (∀ P ∈ (B.C i).arc a, jOver N ℂ ∈ P.toValuationSubring) ∧
    ∃ k : Fin R.N, (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' (B.C i).arc a = R.arcSet k ∧
      InjOn (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) ((B.C i).arc a) := by
  have hs (P : Place ℂ F) (hP : P ∈ (B.C i).arc a) : P ∈ (B.C i).ζ.source :=
    ((B.C i).mem_arc_iff_coordinate a P).mp hP |>.1
  refine ⟨fun P hP => (B.sheets.2.1 i P (hs P hP)).1,
    Fin.cast (congrArg RadialRegion.N (B.region_eq i)) a, ?_, ?_⟩
  · rw [RadialRegion.arcSet_cast (B.region_eq i), ← (B.C i).coordinate_arc_image a]
    exact image_congr fun P hP => ((B.sheets.2.1 i P (hs P hP)).2).symm
  · intro P hP Q hQ he
    apply (B.C i).ζ.injOn (hs P hP) (hs Q hQ)
    rw [(B.sheets.2.1 i P (hs P hP)).2, (B.sheets.2.1 i Q (hs Q hQ)).2]
    exact he

theorem OriginalBranchRegionFamily.arc_image {b : ℂ} (B : OriginalBranchRegionFamily N b R)
    (hq : R.q = b) (v : originalPositiveFiber N (jOver N ℂ) b) (a : Fin (B.C v).R.N) :
    (∀ P ∈ (B.C v).arc a, jOver N ℂ ∈ P.toValuationSubring) ∧
    ∃ k : Fin R.N, (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' (B.C v).arc a = R.arcSet k ∧
      InjOn (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) ((B.C v).arc a) := by
  refine ⟨?_, ?_⟩
  · intro P hP
    exact ((B.geometry v).2.2.2 P (((B.C v).mem_arc_iff_coordinate a P).mp hP).1).1
  · apply (B.C v).powered_arc_image (B.geometry v).2.2.1 a
      (fun P => originalPlaceEval N ℂ P (jOver N ℂ))
    intro P hP
    rw [hq]
    exact ((B.geometry v).2.2.2 P hP).2

end
end Dubon2026.SourceFunctionField.CellGeometry
