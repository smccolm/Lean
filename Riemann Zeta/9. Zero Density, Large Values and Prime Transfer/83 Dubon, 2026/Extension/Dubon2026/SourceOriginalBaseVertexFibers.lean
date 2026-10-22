import Dubon2026.SourceOriginalDissectionBaseVertices

/-! DUB-17/18 -> original Abel-Jacobi -> exact dissection vertex count.
Every constructed planar vertex avoids the two branch values, so its full
original j fiber has the proved all-level degree. Distinct base vertices
have disjoint actual fibers; their finite union has the exact product count.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover.BaseVertexData
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} {A : OriginalGlobalCellCover N Marked}
variable (V : A.BaseVertexData)
local notation "F" => modularFunctionFieldOver N ℂ

theorem not_mem_marked {z : ℂ} (hz : z ∈ V.points) : z ∉ insert 0 (insert 1728 Marked) := by
  intro hm
  obtain ⟨j, hj⟩ := V.grid_line z hz
  exact (A.G.D.avoid z hm j).1 hj

theorem fiber_card {z : ℂ} (hz : z ∈ V.points) :
    (originalPositiveFiber N (jOver N ℂ) z).card = SourceLevelProjective.dedekindPsi N := by
  have h0 : z ≠ 0 := fun he => V.not_mem_marked hz (by simp [he])
  have h1728 : z ≠ 1728 := fun he => V.not_mem_marked hz (by simp [he])
  have hne : jOver N ℂ - algebraMap ℂ F z ≠ 0 := by
    intro he
    exact transcendental_jOver N ℂ (sub_eq_zero.mp he ▸ isAlgebraic_algebraMap z)
  let e : {P : Place ℂ F // jOver N ℂ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ) = z} ≃ ↥(originalPositiveFiber N (jOver N ℂ) z) :=
    Equiv.subtypeEquivRight fun P => (OriginalChart.mem_originalPositiveFiber_iff_regular_eval N hne P).symm
  have h := OriginalChart.card_original_j_regular_fiber N z h0 h1728
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe] at h
  exact h

theorem fiber_disjoint {z w : ℂ} (hzw : z ≠ w) :
    Disjoint (originalPositiveFiber N (jOver N ℂ) z) (originalPositiveFiber N (jOver N ℂ) w) := by
  rw [Finset.disjoint_left]
  intro P hz hw
  have hez := originalPlaceEval_eq_of_ord_sub_pos N ℂ P (jOver N ℂ) z
    ((mem_originalPositiveFiber N (jOver N ℂ) z P).mp hz)
  have hew := originalPlaceEval_eq_of_ord_sub_pos N ℂ P (jOver N ℂ) w
    ((mem_originalPositiveFiber N (jOver N ℂ) w P).mp hw)
  exact hzw (hez.symm.trans hew)

/-- The finite union of all actual j fibers over the constructed planar endpoints. -/
def fiberUnion : Finset (Place ℂ F) := by
  classical
  exact V.points.biUnion (originalPositiveFiber N (jOver N ℂ))

theorem fiberUnion_card : V.fiberUnion.card = V.points.card * SourceLevelProjective.dedekindPsi N := by
  classical
  rw [fiberUnion, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun z hz => V.fiber_card hz), Finset.sum_const, nsmul_eq_mul]
    rfl
  · intro z _ w _ hzw
    exact fiber_disjoint hzw

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover.BaseVertexData
