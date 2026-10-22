import Dubon2026.SourceCellGridSquareBounds
import Dubon2026.SourceCellGridSeparation

/-! DUB-17/18 -> original Abel-Jacobi -> finite paired cell dissection.
Construct a finite grid window containing all marked and branch values, with
prescribed small mesh, exact branch-square assignment and marked centers.
The ordinary-square lifting theorem removes the source's auxiliary local
sheet-scale construction; only these finite planar conditions are needed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
noncomputable section
open Set

/-- Finite grid geometry shared by the actual ordinary, branch and pole cells. -/
structure FiniteLayout (M : Finset ℂ) (δ B : ℝ) where
  /-- Shared offset of the horizontal and vertical grid lines. -/
  o : ℝ
  /-- Positive mesh size. -/
  h : ℝ
  /-- Lowest square index in either coordinate. -/
  lo : ℤ
  /-- Highest square index in either coordinate. -/
  hi : ℤ
  /-- Radius containing the marked values and the prescribed pole bound. -/
  R : ℝ
  /-- Interior centers, prescribed at every marked value. -/
  center : ℤ × ℤ → ℂ
  /-- The branch value in a square, if one exists. -/
  capAt : ℤ × ℤ → Option ℂ
  mesh_pos : 0 < h
  mesh_lt : h < δ
  window_nontrivial : lo + 1 < hi
  radius_one : 1 < R
  radius_bound : B < R
  outer_lower : o + lo * h < -R
  outer_upper : R < o + (hi + 1) * h
  inner_lower : o + (lo + 1) * h ≤ -R
  inner_upper : R < o + hi * h
  marked_bound : ∀ m ∈ M, ‖m‖ < R - 1
  avoid : ∀ m ∈ M, ∀ j : ℤ, m.re - o ≠ j * h ∧ m.im - o ≠ j * h
  separate : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' →
    ⌊(m.re - o) / h⌋ = ⌊(m'.re - o) / h⌋ →
    ⌊(m.im - o) / h⌋ = ⌊(m'.im - o) / h⌋ → False
  center_inside : ∀ p : ℤ × ℤ,
    (o + p.1 * h < (center p).re ∧ (center p).re < o + (p.1 + 1) * h) ∧
    (o + p.2 * h < (center p).im ∧ (center p).im < o + (p.2 + 1) * h)
  center_right_zero : ∀ p : ℤ × ℤ, p.1 = hi →
    o + p.2 * h < 0 → 0 < o + (p.2 + 1) * h → (center p).im = 0
  center_marked : ∀ m ∈ M, center (⌊(m.re - o) / h⌋, ⌊(m.im - o) / h⌋) = m
  cap_exact : ∀ (p : ℤ × ℤ) (b : ℂ), capAt p = some b ↔
    b ∈ ({0, 1728} : Finset ℂ) ∧ ⌊(b.re - o) / h⌋ = p.1 ∧ ⌊(b.im - o) / h⌋ = p.2

theorem exists_finite_layout (M : Finset ℂ) {δ : ℝ} (hδ : 0 < δ) (B : ℝ)
    (hBad : ({0, 1728} : Finset ℂ) ⊆ M) : Nonempty (FiniteLayout M δ B) := by
  classical
  obtain ⟨o, h, hh, hhδ, hav, hsep⟩ := exists_separating_grid M hδ
  let R := 2 + |B| + ∑ m ∈ M, ‖m‖
  have hsum : 0 ≤ ∑ m ∈ M, ‖m‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hR : 1 < R := by dsimp [R]; linarith [abs_nonneg B]
  have hBR : B < R := by dsimp [R]; linarith [le_abs_self B, abs_nonneg B]
  have hM : ∀ m ∈ M, ‖m‖ < R - 1 := by
    intro m hm
    have hs := Finset.single_le_sum (fun z (_ : z ∈ M) => norm_nonneg z) hm
    dsimp [R]
    linarith [abs_nonneg B]
  obtain ⟨lo, hi, hlh, hlow, hupp, hilow, hiupp, _, _⟩ := exists_window hh (by linarith : 0 < R)
  have hcol : ∀ m ∈ M, ⌊(m.re - o) / h⌋ ≠ hi := by
    intro m hm
    exact ne_of_lt (floor_mem_inner hh hilow hiupp (hM m hm)).2.1
  obtain ⟨center, hcenter, hright, hmarked⟩ := exists_centre M hh hi hav hsep hcol
  obtain ⟨capAt, hcap⟩ := exists_capAt {0, 1728} o h
    (fun b hb b' hb' hne => hsep b (hBad hb) b' (hBad hb') hne)
  exact ⟨{
    o := o
    h := h
    lo := lo
    hi := hi
    R := R
    center := center
    capAt := capAt
    mesh_pos := hh
    mesh_lt := hhδ
    window_nontrivial := hlh
    radius_one := hR
    radius_bound := hBR
    outer_lower := hlow
    outer_upper := hupp
    inner_lower := hilow
    inner_upper := hiupp
    marked_bound := hM
    avoid := hav
    separate := hsep
    center_inside := hcenter
    center_right_zero := hright
    center_marked := hmarked
    cap_exact := hcap }⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
