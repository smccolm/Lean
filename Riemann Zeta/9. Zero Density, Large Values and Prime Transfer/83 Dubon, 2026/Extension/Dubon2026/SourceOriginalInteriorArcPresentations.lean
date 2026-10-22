import Dubon2026.SourceOriginalArcPresentation

/-! DUB-17/18 -> original Abel-Jacobi -> C1 reversal of actual interior arcs.
Construct the positive affine presentation for each ordinary or branch arc
of the actual global cover, using its existing sheet or power coordinates.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem ordinary_arc_presentation (p : A.G.PlainIndex)
    (i : Fin (SourceLevelProjective.dedekindPsi N)) (a : Fin ((A.G.ordinary p.1 p.2).C i).R.N) :
    ∃ (k : Fin (A.G.region p.1).N) (m c : ℝ),
      A.SquareArcPresentation ⟨.inl (.inl (p, i)), a⟩ p.1 k m c := by
  let B := A.G.ordinary p.1 p.2
  let C := B.C i
  let k : Fin (A.G.region p.1).N := Fin.cast (congrArg RadialRegion.N (B.region_eq i)) a
  obtain ⟨hs, ht⟩ := RadialRegion.arc_parameters_cast (B.region_eq i) a
  have hr (P : Place ℂ F) (hP : P ∈ C.arc a) :=
    B.sheets.2.1 i P ((C.mem_arc_iff_coordinate a P).mp hP).1
  have himg : (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' C.arc a =
      (A.G.region p.1).arcSet k := by
    rw [RadialRegion.arcSet_cast (B.region_eq i), ← C.coordinate_arc_image a]
    exact image_congr fun P hP => (hr P hP).2.symm
  refine ⟨k, 1, 0, rfl, zero_lt_one, ?_, ?_, ?_, LiesOver.of_image_eq (fun P hP => (hr P hP).1) himg⟩
  · simpa only [one_mul, add_zero] using hs.symm
  · simpa only [one_mul, add_zero] using ht.symm
  · intro t _
    obtain ⟨hsrc, hcoord⟩ := C.bdry_source_and_coordinate t
    change originalPlaceEval N ℂ (C.bdry t) (jOver N ℂ) = (A.G.region p.1).loop (1 * t + 0)
    rw [one_mul, add_zero, ← (B.sheets.2.1 i _ hsrc).2, hcoord]
    exact congrArg (fun R : RadialRegion => R.loop t) (B.region_eq i)

theorem branch_arc_presentation (b : ({0, 1728} : Finset ℂ))
    (v : originalPositiveFiber N (jOver N ℂ) b)
    (a : Fin ((A.G.branch (A.G.branchSquare b) b (A.G.branch_cap b)).C v).R.N) :
    ∃ (k : Fin (A.G.region (A.G.branchSquare b)).N) (m c : ℝ),
      A.SquareArcPresentation ⟨.inl (.inr ⟨b, v⟩), a⟩ (A.G.branchSquare b) k m c := by
  let B := A.G.branch (A.G.branchSquare b) b (A.G.branch_cap b)
  let C := B.C v
  have hq := A.branch_region_center (A.G.branchSquare b) b (A.G.branch_cap b)
  obtain ⟨k, m, c, hm, hs, ht, hloop, himg⟩ := (B.geometry v).2.2.1.arc_presentation a
  have hread (P : Place ℂ F) (hP : P ∈ C.ζ.source) :
      originalPlaceEval N ℂ P (jOver N ℂ) = (A.G.region (A.G.branchSquare b)).q +
        C.ζ P ^ ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat := by
    rw [hq]
    exact ((B.geometry v).2.2.2 P hP).2
  have hcoord : (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' C.arc a =
      (fun u : ℂ => (A.G.region (A.G.branchSquare b)).q +
        u ^ ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat) '' C.R.arcSet a := by
    rw [← C.coordinate_arc_image a, image_image]
    exact image_congr fun P hP => hread P ((C.mem_arc_iff_coordinate a P).mp hP).1
  refine ⟨k, m, c, rfl, hm, hs, ht, ?_, ?_⟩
  · intro t _
    obtain ⟨hsrc, hco⟩ := C.bdry_source_and_coordinate t
    change originalPlaceEval N ℂ (C.bdry t) (jOver N ℂ) = _
    rw [hread _ hsrc, hco]
    exact hloop t
  · apply LiesOver.of_image_eq _ (hcoord.trans himg)
    intro P hP
    exact ((B.geometry v).2.2.2 P ((C.mem_arc_iff_coordinate a P).mp hP).1).1

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
