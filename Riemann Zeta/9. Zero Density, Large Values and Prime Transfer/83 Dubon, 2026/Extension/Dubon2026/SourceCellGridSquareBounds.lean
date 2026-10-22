import Dubon2026.SourceCellMarkedGridCentres

/-! DUB-17/18 -> original Abel-Jacobi -> finite paired cell dissection.
These bounds place branch squares inside the already constructed normal
neighborhoods and prove that the finite window covers its closed rectangle.
No new covering or ramification premise is introduced.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
noncomputable section
open Set

theorem mem_gridSquare_floor {o h : ℝ} (hh : 0 < h) (z : ℂ) :
    z ∈ gridSquare o h ⌊(z.re - o) / h⌋ ⌊(z.im - o) / h⌋ := by
  have key (x : ℝ) : o + ⌊(x - o) / h⌋ * h ≤ x ∧
      x ≤ o + ((⌊(x - o) / h⌋ : ℤ) + 1) * h := by
    have ha := (le_div_iff₀ hh).mp (Int.floor_le ((x - o) / h))
    have hb := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((x - o) / h))
    constructor <;> linarith
  exact ⟨key z.re, key z.im⟩

theorem dist_le_two_mul_of_mem {o h : ℝ} {j k : ℤ} {z b : ℂ}
    (hz : z ∈ gridSquare o h j k) (hb : b ∈ gridSquare o h j k) :
    dist z b ≤ 2 * h := by
  calc
    dist z b ≤ dist z ⟨o + (j + 1 / 2) * h, o + (k + 1 / 2) * h⟩ +
        dist ⟨o + (j + 1 / 2) * h, o + (k + 1 / 2) * h⟩ b := dist_triangle _ _ _
    _ ≤ h + h := add_le_add (dist_mid_le hz) (by simpa only [dist_comm] using dist_mid_le hb)
    _ = 2 * h := by ring

theorem gridSquare_subset_ball {o h ε : ℝ} {j k : ℤ} {b : ℂ}
    (hb : b ∈ gridSquare o h j k) (hε : 2 * h < ε) :
    gridSquare o h j k ⊆ Metric.ball b ε := by
  intro z hz
  exact (dist_le_two_mul_of_mem hz hb).trans_lt hε

theorem exists_window_square {o h : ℝ} (hh : 0 < h) {lo hi : ℤ} (hlh : lo ≤ hi)
    {z : ℂ} (hz : z.re ∈ Icc (o + lo * h) (o + (hi + 1) * h) ∧
      z.im ∈ Icc (o + lo * h) (o + (hi + 1) * h)) :
    ∃ j ∈ Icc lo hi, ∃ k ∈ Icc lo hi, z ∈ gridSquare o h j k := by
  have key (x : ℝ) (hx : x ∈ Icc (o + lo * h) (o + (hi + 1) * h)) :
      ∃ j ∈ Icc lo hi, x ∈ Icc (o + j * h) (o + (j + 1) * h) := by
    by_cases ht : x < o + (hi + 1) * h
    · refine ⟨⌊(x - o) / h⌋, ⟨?_, ?_⟩, ?_, ?_⟩
      · rw [Int.le_floor, le_div_iff₀ hh]
        linarith [hx.1]
      · have hi' : ⌊(x - o) / h⌋ < hi + 1 := by
          rw [Int.floor_lt, div_lt_iff₀ hh]
          push_cast
          linarith
        omega
      · have ha := (le_div_iff₀ hh).mp (Int.floor_le ((x - o) / h))
        linarith
      · have ha := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((x - o) / h))
        linarith
    · refine ⟨hi, ⟨hlh, le_rfl⟩, ?_, hx.2⟩
      have he : x = o + (hi + 1) * h := le_antisymm hx.2 (le_of_not_gt ht)
      rw [he]
      linarith
  obtain ⟨j, hj, hx⟩ := key z.re hz.1
  obtain ⟨k, hk, hy⟩ := key z.im hz.2
  exact ⟨j, hj, k, hk, hx, hy⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
