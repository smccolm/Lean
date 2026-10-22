import Dubon2026.SourceOriginalPoleMarkedCenters

/-! DUB-17/18 -> original Abel-Jacobi -> the source marked cell dissection.
Apply the actual j grid to the evaluations of an arbitrary finite set of
original places and a prescribed base point. Every marked place lies at a
cell center in its interior, and each cell carrier meets the marked set in
at most one place. Pairing, intersection chains and Euler remain required.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_centered_global_cover (P₀ : Place ℂ F) (S : Finset (Place ℂ F)) :
    ∃ (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked),
      (∀ P : Place ℂ F, ∃ i : A.Index, P ∈ (A.cell i).carrier) ∧
      (∀ P ∈ insert P₀ (S : Set (Place ℂ F)), ∃ i : A.Index,
        P ∈ (A.cell i).interior' ∧ (A.cell i).ζ P = (A.cell i).R.q) ∧
      (∀ i : A.Index, ((A.cell i).carrier ∩ (S : Set (Place ℂ F))).Subsingleton) := by
  classical
  let Marked := (insert P₀ S).image (fun P => originalPlaceEval N ℂ P (jOver N ℂ))
  obtain ⟨A, hcover⟩ := exists_original_global_cell_cover N Marked
  have hm (P : Place ℂ F) (hP : P ∈ insert P₀ (S : Set (Place ℂ F))) :
      originalPlaceEval N ℂ P (jOver N ℂ) ∈ insert 0 (insert 1728 Marked) := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨P, by simpa only [Finset.mem_insert, Finset.mem_coe, mem_insert_iff] using hP, rfl⟩
  refine ⟨Marked, A, hcover, ?_, ?_⟩
  · intro P hP
    obtain ⟨i, hi⟩ := hcover P
    have hc := A.marked_center i P hi (fun _ => hm P hP)
    exact ⟨i, (A.cell i).center_interior hi hc, hc⟩
  · intro i P hP Q hQ
    have hp := A.marked_center i P hP.1 (fun _ => hm P (Or.inr hP.2))
    have hq := A.marked_center i Q hQ.1 (fun _ => hm Q (Or.inr hQ.2))
    exact (A.cell i).eq_of_coordinate_eq hP.1 hQ.1 (hp.trans hq.symm)

end
end Dubon2026.SourceFunctionField.CellGeometry
