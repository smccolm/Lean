import Dubon2026.SourceOriginalInteriorArcPresentations

/-! DUB-17/18 -> original Abel-Jacobi -> C1 reversal of actual exterior arcs.
Compose the proved positive power-lap parameter with reciprocal reversal.
Actual inverse-j evaluation gives the j boundary formula without an added
regularity or coordinate hypothesis; full side coverage is preserved.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
open scoped Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exterior_arc_presentation (v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0)
    (a : Fin (A.poles.C v).R.N) :
    ∃ (k : Fin A.W.R.N) (m c : ℝ), A.ExteriorArcPresentation ⟨.inr v, a⟩ k m c := by
  let B := A.poles
  let C := B.C v
  obtain ⟨k, m, c, hm, hs, ht, hloop, himg⟩ := (B.geometry v).2.2.1.arc_presentation a
  obtain ⟨k₀, hks, hkt, hrloop, hrimg⟩ := B.reciprocal.arc_presentation k
  have hread (P : Place ℂ F) (hP : P ∈ C.ζ.source) :
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = B.R.q + C.ζ P ^
        ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat := by
    rw [B.reciprocal.1, zero_add]
    exact ((B.geometry v).2.2.2 P hP).2
  have hcoord : (fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) '' C.arc a =
      B.R.arcSet k := by
    rw [← himg, ← C.coordinate_arc_image a, image_image]
    exact image_congr fun P hP => hread P ((C.mem_arc_iff_coordinate a P).mp hP).1
  have hjimg : (fun P => originalPlaceEval N ℂ P (jOver N ℂ)) '' C.arc a = A.W.R.arcSet k₀ := by
    calc
      _ = (fun z : ℂ => z⁻¹) '' ((fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) '' C.arc a) := by
        rw [image_image]
        apply image_congr
        intro P _
        exact (by rw [originalPlaceEval_inv, inv_inv])
      _ = _ := by rw [hcoord]; exact hrimg
  refine ⟨k₀, -m, 2 * π - c, rfl, neg_neg_of_pos hm, ?_, ?_, ?_, ?_⟩
  · change -m * C.R.φs a.castSucc + (2 * π - c) = _
    linarith
  · change -m * C.R.φs a.succ + (2 * π - c) = _
    linarith
  · intro t _
    obtain ⟨hsrc, hco⟩ := C.bdry_source_and_coordinate t
    change originalPlaceEval N ℂ (C.bdry t) (jOver N ℂ) = _
    calc
      _ = (originalPlaceEval N ℂ (C.bdry t) (jOver N ℂ)⁻¹)⁻¹ := by rw [originalPlaceEval_inv, inv_inv]
      _ = (B.R.loop (m * t + c))⁻¹ := by rw [hread _ hsrc, hco, hloop]
      _ = A.W.R.loop (-m * t + (2 * π - c)) := by rw [hrloop]; congr 1; ring
  · exact LiesOver.of_image_eq (B.arc_image v a).1 hjimg

theorem exists_arc_presentation (a : A.Arc) :
    (∃ (p : ℤ × ℤ) (k : Fin (A.G.region p).N) (m c : ℝ), A.SquareArcPresentation a p k m c) ∨
    (∃ (k : Fin A.W.R.N) (m c : ℝ), A.ExteriorArcPresentation a k m c) := by
  rcases a with ⟨i, k⟩
  rcases i with (⟨p, i⟩ | ⟨b, v⟩) | v
  · obtain ⟨a, m, c, h⟩ := A.ordinary_arc_presentation p i k
    exact Or.inl ⟨p.1, a, m, c, h⟩
  · obtain ⟨a, m, c, h⟩ := A.branch_arc_presentation b v k
    exact Or.inl ⟨A.G.branchSquare b, a, m, c, h⟩
  · exact Or.inr (A.exterior_arc_presentation v k)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
