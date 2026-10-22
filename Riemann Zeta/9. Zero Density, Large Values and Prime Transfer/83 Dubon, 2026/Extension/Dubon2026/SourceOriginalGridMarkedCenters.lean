import Dubon2026.SourceOriginalCellCenters

/-! DUB-17/18 -> original Abel-Jacobi -> centered marked dissection.
Grid separation forces every selected j value in an ordinary or branch
cell to equal its prescribed center value. Actual sheet coordinates and
actual power coordinates then identify the unique original cell center.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (G : OriginalJFiniteGrid N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem ordinary_marked_center (p : ℤ × ℤ) (hp : G.D.capAt p = none)
    (i : Fin (SourceLevelProjective.dedekindPsi N)) (P : Place ℂ F)
    (hP : P ∈ ((G.ordinary p hp).C i).carrier)
    (hm : originalPlaceEval N ℂ P (jOver N ℂ) ∈ insert 0 (insert 1728 Marked)) :
    ((G.ordinary p hp).C i).ζ P = ((G.ordinary p hp).C i).R.q := by
  obtain ⟨_, hregion⟩ := ((G.ordinary p hp).coverage P).mpr ⟨i, hP⟩
  have hsquare : originalPlaceEval N ℂ P (jOver N ℂ) ∈
      SquareGrid.gridSquare G.D.o G.D.h p.1 p.2 := by
    rw [(G.rectangle p).2.2.1] at hregion
    exact hregion
  have hf := SquareGrid.floor_eq_of_mem G.D.mesh_pos (G.D.avoid _ hm) hsquare
  have hctr : G.D.center p = originalPlaceEval N ℂ P (jOver N ℂ) := by
    simpa only [hf.1, hf.2, Prod.eta] using G.D.center_marked _ hm
  have hsource := ((((G.ordinary p hp).C i).mem_carrier_iff_coordinate P).mp hP).1
  have he := ((G.ordinary p hp).sheets.2.1 i P hsource).2
  rw [(G.ordinary p hp).region_eq i, (G.rectangle p).1, hctr]
  exact he

theorem branch_marked_center (b : ({0, 1728} : Finset ℂ))
    (v : originalPositiveFiber N (jOver N ℂ) b) (P : Place ℂ F)
    (hP : P ∈ ((G.branch (G.branchSquare b) b (G.branch_cap b)).C v).carrier)
    (hm : originalPlaceEval N ℂ P (jOver N ℂ) ∈ insert 0 (insert 1728 Marked)) :
    ((G.branch (G.branchSquare b) b (G.branch_cap b)).C v).ζ P =
      ((G.branch (G.branchSquare b) b (G.branch_cap b)).C v).R.q := by
  let A := G.branch (G.branchSquare b) b (G.branch_cap b)
  obtain ⟨_, hregion⟩ := (A.coverage P).mpr ⟨v, hP⟩
  have hsquare : originalPlaceEval N ℂ P (jOver N ℂ) ∈
      SquareGrid.gridSquare G.D.o G.D.h (G.branchSquare b).1 (G.branchSquare b).2 := by
    rw [(G.rectangle (G.branchSquare b)).2.2.1] at hregion
    exact hregion
  have hf := SquareGrid.floor_eq_of_mem G.D.mesh_pos (G.D.avoid _ hm) hsquare
  have hb : b.val ∈ insert 0 (insert 1728 Marked) := by
    have h := b.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    tauto
  have hval : originalPlaceEval N ℂ P (jOver N ℂ) = b := by
    by_contra hne
    exact G.D.separate _ hm b hb hne hf.1 hf.2
  have hsource := (((A.C v).mem_carrier_iff_coordinate P).mp hP).1
  have he := ((A.geometry v).2.2.2 P hsource).2
  rw [hval] at he
  have hz : (A.C v).ζ P ^ ((v : Place ℂ F).ord (jOver N ℂ - algebraMap ℂ F b)).toNat = 0 :=
    add_left_cancel (he.symm.trans (add_zero (b : ℂ)).symm)
  have hcoord : (A.C v).ζ P = 0 := (pow_eq_zero_iff'.mp hz).1
  exact hcoord.trans (A.geometry v).2.2.1.1.symm

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
