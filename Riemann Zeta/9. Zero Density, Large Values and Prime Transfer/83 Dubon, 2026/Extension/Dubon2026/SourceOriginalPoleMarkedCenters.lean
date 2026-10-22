import Dubon2026.SourceOriginalGridMarkedCenters

/-! DUB-17/18 -> original Abel-Jacobi -> marked exterior cells.
Every marked regular j value is strictly inside the outer window. Thus a
marked point on a pole-cell carrier is an actual pole. The original inverse
j evaluation and its exact power coordinate put it at that cell's center.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem marked_value_inside_window {z : ℂ} (hz : z ∈ insert 0 (insert 1728 Marked)) :
    z ∈ A.W.R.Kint := by
  rw [A.W.Kint_eq]
  exact SquareGrid.window_contains A.G.D.outer_lower A.G.D.outer_upper z
    ((A.G.D.marked_bound z hz).le.trans (sub_le_self _ zero_le_one))

theorem pole_marked_center (v : originalPositiveFiber N (jOver N ℂ)⁻¹ 0) (P : Place ℂ F)
    (hP : P ∈ (A.poles.C v).carrier)
    (hm : jOver N ℂ ∈ P.toValuationSubring →
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ insert 0 (insert 1728 Marked)) :
    (A.poles.C v).ζ P = (A.poles.C v).R.q := by
  have hn : jOver N ℂ ∉ P.toValuationSubring := by
    rcases (A.poles.coverage P).mpr ⟨v, hP⟩ with hp | ⟨hr, hout⟩
    · exact hp
    · exact (hout (A.marked_value_inside_window (hm hr))).elim
  have ho : P.ord (jOver N ℂ) < 0 := by
    by_contra h
    exact hn (P.mem_of_ord_nonneg (le_of_not_gt h))
  have hs := (((A.poles.C v).mem_carrier_iff_coordinate P).mp hP).1
  obtain ⟨hinv, hval⟩ := (A.poles.geometry v).2.2.2 P hs
  have hj : jOver N ℂ ≠ 0 := fun hz => transcendental_jOver N ℂ (hz ▸ isAlgebraic_zero)
  have hz : originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = 0 :=
    (originalPlaceEval_eq_zero_iff_ord_pos N ℂ P hinv (inv_ne_zero hj)).mpr
      (by rw [Place.ord_inv]; omega)
  have hcoord : (A.poles.C v).ζ P = 0 := (pow_eq_zero_iff'.mp (hval.symm.trans hz)).1
  exact hcoord.trans (A.poles.geometry v).2.2.1.1.symm

theorem marked_center (i : A.Index) (P : Place ℂ F) (hP : P ∈ (A.cell i).carrier)
    (hm : jOver N ℂ ∈ P.toValuationSubring →
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ insert 0 (insert 1728 Marked)) :
    (A.cell i).ζ P = (A.cell i).R.q := by
  cases i with
  | inl i =>
    have hr : jOver N ℂ ∈ P.toValuationSubring :=
      ((A.G.interiorCell_coverage P).mpr ⟨i, hP⟩).1
    cases i with
    | inl p => exact A.G.ordinary_marked_center p.1.1 p.1.2 p.2 P hP (hm hr)
    | inr p => exact A.G.branch_marked_center p.1 p.2 P hP (hm hr)
  | inr v => exact A.pole_marked_center v P hP hm

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
