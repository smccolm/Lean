import Dubon2026.SourceOriginalGridCellFamilies

/-! DUB-17/18 -> original Abel-Jacobi -> source finite paired dissection.
Construct the grid and all ordinary and ramified cells together, retaining
shared base rectangles and the pole scale. No grid, normal-coordinate scale,
ordinary sheet family or branch-cell family is supplied by a caller.
Global edge pairing, Euler counting and raw reciprocity remain separate.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]

/-- Original j cells on one compatible finite grid, with an adequate exterior pole scale. -/
structure OriginalJFiniteGrid (Marked : Finset ℂ) where
  /-- Upper bound for the mesh imposed by the actual branch charts. -/
  δ : ℝ
  /-- Radius beyond which the actual pole cells exhaust the curve. -/
  B : ℝ
  delta_pos : 0 < δ
  delta_le_one : δ ≤ 1
  pole_pos : 0 < B
  /-- Constructed finite grid avoiding and separating all selected values. -/
  D : SquareGrid.FiniteLayout (insert 0 (insert 1728 Marked)) δ B
  /-- Shared six-arc base rectangle for each square. -/
  region : ℤ × ℤ → RadialRegion
  rectangle : ∀ p : ℤ × ℤ,
    RectSixArcs.RectangleGeometry (D.o + p.1 * D.h) (D.o + (p.1 + 1) * D.h)
      (D.o + p.2 * D.h) (D.o + (p.2 + 1) * D.h) (D.center p)
      (D.leftSplit p) (region p)
  /-- Actual analytic sheet cells over each ordinary square. -/
  ordinary : ∀ p : ℤ × ℤ, D.capAt p = none → OriginalOrdinaryRegionFamily N (region p)
  /-- Actual powered cells over each branch square. -/
  branch : ∀ (p : ℤ × ℤ) (b : ℂ), D.capAt p = some b → OriginalBranchRegionFamily N b (region p)
  /-- Actual exterior cells for each sufficiently large radial window. -/
  pole : ∀ W : RadialRegion, W.q = 0 → 2 ≤ W.N → Metric.closedBall 0 B ⊆ W.Kint →
    OriginalPoleRegionFamily N W

theorem exists_original_j_finite_grid (Marked : Finset ℂ) :
    Nonempty (OriginalJFiniteGrid N Marked) := by
  classical
  obtain ⟨ε0, hε0, hc0⟩ := exists_original_branch_region_family N 0
  obtain ⟨ε1728, hε1728, hc1728⟩ := exists_original_branch_region_family N 1728
  obtain ⟨B, hB, hpole⟩ := exists_original_pole_region_family N
  let δ := min 1 (min (ε0 / 4) (ε1728 / 4))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ0 : δ ≤ ε0 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1728 : δ ≤ ε1728 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hBad : ({0, 1728} : Finset ℂ) ⊆ insert 0 (insert 1728 Marked) := by
    intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
    rcases hb with rfl | rfl <;> simp
  obtain ⟨D⟩ := SquareGrid.exists_finite_layout (insert 0 (insert 1728 Marked)) hδ B hBad
  have hr : ∀ p : ℤ × ℤ, ∃ R : RadialRegion,
      RectSixArcs.RectangleGeometry (D.o + p.1 * D.h) (D.o + (p.1 + 1) * D.h)
        (D.o + p.2 * D.h) (D.o + (p.2 + 1) * D.h) (D.center p)
        (D.leftSplit p) R := by
    intro p
    exact RectSixArcs.exists_rect_sixArcs _ _ _ _ _ _
      (D.center_inside p).1.1 (D.center_inside p).1.2
      (D.center_inside p).2.1 (D.center_inside p).2.2
      (D.leftSplit_inside p).1 (D.leftSplit_inside p).2
  choose R hR using hr
  have hord : ∀ p : ℤ × ℤ, D.capAt p = none → Nonempty (OriginalOrdinaryRegionFamily N (R p)) := by
    intro p hp
    have hn := (D.cap_none_iff hBad p).mp hp
    exact exists_original_ordinary_region_family N D.mesh_pos p.1 p.2 (R p) (hR p).2.2.1
      (hn 0 (by simp)) (hn 1728 (by simp))
  have hbran : ∀ (p : ℤ × ℤ) (b : ℂ), D.capAt p = some b →
      Nonempty (OriginalBranchRegionFamily N b (R p)) := by
    intro p b hb
    have hq : (R p).q = b := (hR p).1.trans (D.cap_center hBad hb)
    have hN : 2 ≤ (R p).N := by rw [(hR p).2.1]; norm_num
    have hmem : b = 0 ∨ b = 1728 := by simpa using ((D.cap_exact p b).mp hb).1
    rcases hmem with rfl | rfl
    · apply hc0 (R p) hq hN
      rw [(hR p).2.2.1]
      apply D.cap_square_small (b := 0) _ hb
      have hm := D.mesh_lt.trans_le hδ0
      linarith
    · apply hc1728 (R p) hq hN
      rw [(hR p).2.2.1]
      apply D.cap_square_small (b := 1728) _ hb
      have hm := D.mesh_lt.trans_le hδ1728
      linarith
  exact ⟨{
    δ := δ
    B := B
    delta_pos := hδ
    delta_le_one := hδ1
    pole_pos := hB
    D := D
    region := R
    rectangle := hR
    ordinary := fun p hp => Classical.choice (hord p hp)
    branch := fun p b hb => Classical.choice (hbran p b hb)
    pole := fun W hq hN hK => Classical.choice (hpole W hq hN hK) }⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
