import Dubon2026.SourceCellGridSquares

/-! DUB-17/18 -> original Abel-Jacobi -> finite geometric cell assembly.
The finite grid window, unique interior indices, marked centers and branch
square assignment link the proved ordinary, branch and pole cells into one
source-compatible finite family. The unused slit-ray and local-cover scale
arguments are omitted: actual ordinary squares already have convex lifts.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
noncomputable section
open Set

theorem exists_window {o h R : ℝ} (hh : 0 < h) (hR : 0 < R) :
    ∃ lo hi : ℤ, lo + 1 < hi ∧ o + lo * h < -R ∧ R < o + (hi + 1) * h ∧
      o + (lo + 1) * h ≤ -R ∧ R < o + hi * h ∧ -R - 2 * h < o + lo * h ∧
      o + (hi + 1) * h ≤ R + 2 * h := by
  have ha1 : (⌊(-R - o) / h⌋ : ℝ) * h ≤ -R - o := (le_div_iff₀ hh).mp (Int.floor_le ((-R - o) / h))
  have ha2 : -R - o < ((⌊(-R - o) / h⌋ : ℝ) + 1) * h :=
    (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((-R - o) / h))
  have hc1 : (⌊(R - o) / h⌋ : ℝ) * h ≤ R - o := (le_div_iff₀ hh).mp (Int.floor_le ((R - o) / h))
  have hc2 : R - o < ((⌊(R - o) / h⌋ : ℝ) + 1) * h :=
    (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((R - o) / h))
  have hlt : ⌊(-R - o) / h⌋ < ⌊(R - o) / h⌋ + 1 := by
    have h1 : (⌊(-R - o) / h⌋ : ℝ) * h < ((⌊(R - o) / h⌋ : ℝ) + 1) * h := by linarith
    have h2 : (⌊(-R - o) / h⌋ : ℝ) < (⌊(R - o) / h⌋ : ℝ) + 1 := lt_of_mul_lt_mul_right h1 hh.le
    exact_mod_cast h2
  refine ⟨⌊(-R - o) / h⌋ - 1, ⌊(R - o) / h⌋ + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · push_cast
    nlinarith
  · push_cast
    nlinarith
  · push_cast
    nlinarith
  · push_cast
    nlinarith
  · push_cast
    nlinarith
  · push_cast
    nlinarith

theorem window_contains {o h R : ℝ} {lo hi : ℤ} (h2 : o + lo * h < -R) (h3 : R < o + (hi + 1) * h) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      (o + lo * h < z.re ∧ z.re < o + (hi + 1) * h) ∧ (o + lo * h < z.im ∧ z.im < o + (hi + 1) * h) := by
  intro z hz
  have hre := abs_le.mp (le_trans (Complex.abs_re_le_norm z) hz)
  have him := abs_le.mp (le_trans (Complex.abs_im_le_norm z) hz)
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ⟨by linarith [him.1], by linarith [him.2]⟩⟩

theorem window_inner {o h R : ℝ} {lo hi : ℤ} (h4 : o + (lo + 1) * h ≤ -R) (h5 : R < o + hi * h) :
    ∀ z : ℂ, ‖z‖ < R - 1 →
      (o + (lo + 1) * h < z.re ∧ z.re < o + hi * h) ∧ (o + (lo + 1) * h < z.im ∧ z.im < o + hi * h) := by
  intro z hz
  have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm z) hz)
  have him := abs_lt.mp (lt_of_le_of_lt (Complex.abs_im_le_norm z) hz)
  exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, ⟨by linarith [him.1], by linarith [him.2]⟩⟩

theorem floor_mem_inner {o h R : ℝ} {lo hi : ℤ} (hh : 0 < h) (hlo : o + (lo + 1) * h ≤ -R)
    (hhi : R < o + hi * h) {z : ℂ} (hz : ‖z‖ < R - 1) :
    lo < ⌊(z.re - o) / h⌋ ∧ ⌊(z.re - o) / h⌋ < hi ∧ lo < ⌊(z.im - o) / h⌋ ∧ ⌊(z.im - o) / h⌋ < hi := by
  have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm z) hz)
  have him := abs_lt.mp (lt_of_le_of_lt (Complex.abs_im_le_norm z) hz)
  have k : ∀ y : ℝ, -(R - 1) < y → y < R - 1 → lo < ⌊(y - o) / h⌋ ∧ ⌊(y - o) / h⌋ < hi := by
    intro y hy1 hy2
    constructor
    · have h1 : lo + 1 ≤ ⌊(y - o) / h⌋ := by
        rw [Int.le_floor]
        push_cast
        rw [le_div_iff₀ hh]
        nlinarith
      omega
    · rw [Int.floor_lt, div_lt_iff₀ hh]
      nlinarith
  exact ⟨(k z.re hre.1 hre.2).1, (k z.re hre.1 hre.2).2, (k z.im him.1 him.2).1, (k z.im him.1 him.2).2⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
