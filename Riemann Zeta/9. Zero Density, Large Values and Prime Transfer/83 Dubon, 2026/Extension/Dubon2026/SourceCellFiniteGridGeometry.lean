import Dubon2026.SourceCellFiniteGridLayout

/-! DUB-17/18 -> original Abel-Jacobi -> finite cell assembly.
The constructed layout determines exactly which squares contain a branch
value, puts all such squares away from the window boundary and covers the
whole closed window. These statements feed actual original-place cells.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
noncomputable section
open Set
variable {M : Finset ℂ} {δ B : ℝ} (D : FiniteLayout M δ B)

/-- The source split on a left side: its own center at the outer boundary,
and the left neighbor's center on an interior side. -/
def FiniteLayout.leftSplit (p : ℤ × ℤ) : ℝ :=
  if p.1 = D.lo then (D.center p).im else (D.center (p.1 - 1, p.2)).im

theorem FiniteLayout.leftSplit_inside (p : ℤ × ℤ) :
    D.o + p.2 * D.h < D.leftSplit p ∧ D.leftSplit p < D.o + (p.2 + 1) * D.h := by
  unfold leftSplit
  split_ifs
  · exact (D.center_inside p).2
  · exact (D.center_inside (p.1 - 1, p.2)).2

theorem FiniteLayout.marked_inner {m : ℂ} (hm : m ∈ M) :
    D.lo < ⌊(m.re - D.o) / D.h⌋ ∧ ⌊(m.re - D.o) / D.h⌋ < D.hi ∧
    D.lo < ⌊(m.im - D.o) / D.h⌋ ∧ ⌊(m.im - D.o) / D.h⌋ < D.hi :=
  floor_mem_inner D.mesh_pos D.inner_lower D.inner_upper (D.marked_bound m hm)

theorem FiniteLayout.cap_none_iff (hBad : ({0, 1728} : Finset ℂ) ⊆ M) (p : ℤ × ℤ) :
    D.capAt p = none ↔ ∀ b ∈ ({0, 1728} : Finset ℂ),
      b ∉ gridSquare D.o D.h p.1 p.2 := by
  constructor
  · intro hn b hb hmem
    obtain ⟨hx, hy⟩ := floor_eq_of_mem D.mesh_pos (D.avoid b (hBad hb)) hmem
    have hs := (D.cap_exact p b).mpr ⟨hb, hx, hy⟩
    rw [hn] at hs
    cases hs
  · intro hnone
    cases he : D.capAt p with
    | none => rfl
    | some b =>
      obtain ⟨hb, hx, hy⟩ := (D.cap_exact p b).mp he
      have hmem := mem_gridSquare_floor (o := D.o) D.mesh_pos b
      rw [hx, hy] at hmem
      exact (hnone b hb hmem).elim

theorem FiniteLayout.perimeter_plain (hBad : ({0, 1728} : Finset ℂ) ⊆ M)
    {p : ℤ × ℤ} (hp : p.1 = D.lo ∨ p.1 = D.hi ∨ p.2 = D.lo ∨ p.2 = D.hi) :
    D.capAt p = none := by
  cases he : D.capAt p with
  | none => rfl
  | some b =>
    obtain ⟨hb, hx, hy⟩ := (D.cap_exact p b).mp he
    have hi := D.marked_inner (hBad hb)
    rw [hx, hy] at hi
    rcases hp with hp | hp | hp | hp <;> omega

theorem FiniteLayout.cap_center (hBad : ({0, 1728} : Finset ℂ) ⊆ M)
    {p : ℤ × ℤ} {b : ℂ} (hb : D.capAt p = some b) : D.center p = b := by
  obtain ⟨hbM, hx, hy⟩ := (D.cap_exact p b).mp hb
  have hc := D.center_marked b (hBad hbM)
  simpa only [hx, hy, Prod.eta] using hc

theorem FiniteLayout.cap_square_small {ε : ℝ} (hε : 2 * D.h < ε)
    {p : ℤ × ℤ} {b : ℂ} (hb : D.capAt p = some b) :
    gridSquare D.o D.h p.1 p.2 ⊆ Metric.ball b ε := by
  obtain ⟨_, hx, hy⟩ := (D.cap_exact p b).mp hb
  have hmem := mem_gridSquare_floor (o := D.o) D.mesh_pos b
  rw [hx, hy] at hmem
  exact gridSquare_subset_ball hmem hε

theorem FiniteLayout.closedBall_inside {z : ℂ} (hz : ‖z‖ ≤ B) :
    z.re ∈ Ioo (D.o + D.lo * D.h) (D.o + (D.hi + 1) * D.h) ∧
    z.im ∈ Ioo (D.o + D.lo * D.h) (D.o + (D.hi + 1) * D.h) :=
  window_contains D.outer_lower D.outer_upper z (hz.trans D.radius_bound.le)

theorem FiniteLayout.window_covered {z : ℂ}
    (hz : z.re ∈ Icc (D.o + D.lo * D.h) (D.o + (D.hi + 1) * D.h) ∧
      z.im ∈ Icc (D.o + D.lo * D.h) (D.o + (D.hi + 1) * D.h)) :
    ∃ j ∈ Icc D.lo D.hi, ∃ k ∈ Icc D.lo D.hi,
      z ∈ gridSquare D.o D.h j k :=
  exists_window_square D.mesh_pos (by have := D.window_nontrivial; omega) hz

theorem FiniteLayout.branch_separation (hδ : δ ≤ 1) :
    2 ≤ ⌊(((1728 : ℂ).re - D.o) / D.h)⌋ - ⌊(((0 : ℂ).re - D.o) / D.h)⌋ := by
  apply floor_gap D.mesh_pos
  have hh := D.mesh_lt.trans_le hδ
  norm_num
  linarith

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
