import Dubon2026.SourceCellWindowArcGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow
noncomputable section
open scoped Real
open Set

/-- Finite grid window and its prescribed vertical side splits. -/
structure WinData where
  /-- Shared grid-line offset. -/
  o : ℝ
  /-- Positive mesh size. -/
  hm : ℝ
  hhm : 0 < hm
  /-- Leftmost square index. -/
  jlo : ℤ
  /-- Rightmost square index. -/
  jhi : ℤ
  /-- Lowest square index. -/
  klo : ℤ
  /-- Highest square index. -/
  khi : ℤ
  hj : jlo ≤ jhi
  hk : klo ≤ khi
  /-- Prescribed vertical-side split heights. -/
  cy : ℤ × ℤ → ℝ
  hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm
  hx₀ : o + jlo * hm < 0
  hx₁ : 0 < o + (jhi + 1) * hm
  hy₀ : o + klo * hm < 0
  hy₁ : 0 < o + (khi + 1) * hm
  hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0

namespace WinData

variable (D : WinData)

/-- Left endpoint of the grid window. -/
def X₀ : ℝ := D.o + D.jlo * D.hm

/-- Right endpoint of the grid window. -/
def X₁ : ℝ := D.o + (D.jhi + 1) * D.hm

/-- Lower endpoint of the grid window. -/
def Y₀ : ℝ := D.o + D.klo * D.hm

/-- Upper endpoint of the grid window. -/
def Y₁ : ℝ := D.o + (D.khi + 1) * D.hm

/-- Number of columns in the finite window. -/
def J : ℕ := (D.jhi - D.jlo + 1).toNat

/-- Number of rows in the finite window. -/
def K : ℕ := (D.khi - D.klo + 1).toNat

theorem grid_lt {a b : ℝ} (h : a < b) : D.o + a * D.hm < D.o + b * D.hm := by
  have := mul_lt_mul_of_pos_right h D.hhm
  linarith

theorem grid_le {a b : ℝ} (h : a ≤ b) : D.o + a * D.hm ≤ D.o + b * D.hm := by
  have := mul_le_mul_of_nonneg_right h D.hhm.le
  linarith

theorem lt_of_grid_lt {a b : ℝ} (h : D.o + a * D.hm < D.o + b * D.hm) : a < b :=
  lt_of_mul_lt_mul_right (by linarith) D.hhm.le

theorem eq_of_grid_eq {a b : ℝ} (h : D.o + a * D.hm = D.o + b * D.hm) : a = b :=
  mul_right_cancel₀ D.hhm.ne' (by linarith)

theorem intZ_lt_of_grid_lt {a b : ℤ} (h : D.o + a * D.hm < D.o + b * D.hm) : a < b := by
  exact_mod_cast D.lt_of_grid_lt h

theorem intZ_eq_of_grid_eq {a b : ℤ} (h : D.o + a * D.hm = D.o + b * D.hm) : a = b := by
  exact_mod_cast D.eq_of_grid_eq h

theorem cy_gt (j k : ℤ) : D.o + k * D.hm < D.cy (j, k) := (D.hcy (j, k)).1

theorem cy_lt (j k : ℤ) : D.cy (j, k) < D.o + (k + 1) * D.hm := (D.hcy (j, k)).2

theorem cy_ne_grid (j k m : ℤ) : D.cy (j, k) ≠ D.o + m * D.hm := by
  intro h
  have h1 := D.cy_gt j k
  have h2 := D.cy_lt j k
  rw [h] at h1 h2
  have h3 : k < m := D.intZ_lt_of_grid_lt h1
  have h4 : (m : ℝ) < k + 1 := D.lt_of_grid_lt h2
  have h4' : m < k + 1 := by exact_mod_cast h4
  omega

theorem cy_injective_row (j : ℤ) {k k' : ℤ} (h : D.cy (j, k) = D.cy (j, k')) : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  ·
    have h1 := D.cy_lt j k
    have h2 := D.cy_gt j k'
    have h3 : D.o + (k + 1) * D.hm ≤ D.o + k' * D.hm :=
      D.grid_le (by exact_mod_cast (show k + 1 ≤ k' by omega))
    linarith
  · have h1 := D.cy_lt j k'
    have h2 := D.cy_gt j k
    have h3 : D.o + (k' + 1) * D.hm ≤ D.o + k * D.hm :=
      D.grid_le (by exact_mod_cast (show k' + 1 ≤ k by omega))
    linarith

theorem X₀_lt_X₁ : D.X₀ < D.X₁ := by
  unfold X₀ X₁
  exact D.grid_lt (by have := D.hj; exact_mod_cast (show D.jlo < D.jhi + 1 by omega))

theorem Y₀_lt_Y₁ : D.Y₀ < D.Y₁ := by
  unfold Y₀ Y₁
  exact D.grid_lt (by have := D.hk; exact_mod_cast (show D.klo < D.khi + 1 by omega))

theorem X₀_neg : D.X₀ < 0 := D.hx₀
theorem X₁_pos : 0 < D.X₁ := D.hx₁
theorem Y₀_neg : D.Y₀ < 0 := D.hy₀
theorem Y₁_pos : 0 < D.Y₁ := D.hy₁

theorem gridx_mem {j : ℤ} (hj : j ∈ Finset.Icc D.jlo (D.jhi + 1)) :
    D.o + j * D.hm ∈ Set.Icc D.X₀ D.X₁ := by
  rw [Finset.mem_Icc] at hj
  unfold X₀ X₁
  exact ⟨D.grid_le (by exact_mod_cast hj.1), D.grid_le (by exact_mod_cast hj.2)⟩

theorem gridy_mem {k : ℤ} (hk : k ∈ Finset.Icc D.klo (D.khi + 1)) :
    D.o + k * D.hm ∈ Set.Icc D.Y₀ D.Y₁ := by
  rw [Finset.mem_Icc] at hk
  unfold Y₀ Y₁
  exact ⟨D.grid_le (by exact_mod_cast hk.1), D.grid_le (by exact_mod_cast hk.2)⟩

theorem cy_mem_Ioo (j : ℤ) {k : ℤ} (hk : k ∈ Finset.Icc D.klo D.khi) :
    D.cy (j, k) ∈ Set.Ioo D.Y₀ D.Y₁ := by
  rw [Finset.mem_Icc] at hk
  have h1 := D.cy_gt j k
  have h2 := D.cy_lt j k
  have h3 : D.Y₀ ≤ D.o + k * D.hm := by
    unfold Y₀
    exact D.grid_le (by exact_mod_cast hk.1)
  have h4 : D.o + (k + 1) * D.hm ≤ D.Y₁ := by
    unfold Y₁
    exact D.grid_le (by exact_mod_cast (show k + 1 ≤ D.khi + 1 by omega))
  exact ⟨by linarith, by linarith⟩

theorem cy_mem_Icc (j : ℤ) {k : ℤ} (hk : k ∈ Finset.Icc D.klo D.khi) :
    D.cy (j, k) ∈ Set.Icc D.Y₀ D.Y₁ :=
  Set.Ioo_subset_Icc_self (D.cy_mem_Ioo j hk)

theorem card_Icc_cols : (Finset.Icc D.jlo (D.jhi + 1)).card = D.J + 1 := by
  rw [Int.card_Icc]
  unfold J
  have := D.hj
  omega

theorem card_Icc_rows : (Finset.Icc D.klo (D.khi + 1)).card = D.K + 1 := by
  rw [Int.card_Icc]
  unfold K
  have := D.hk
  omega

theorem card_Icc_cols' : (Finset.Icc D.jlo D.jhi).card = D.J := by
  rw [Int.card_Icc]
  unfold J
  have := D.hj
  omega

theorem card_Icc_rows' : (Finset.Icc D.klo D.khi).card = D.K := by
  rw [Int.card_Icc]
  unfold K
  have := D.hk
  omega

theorem K_pos : 0 < D.K := by
  unfold K
  have := D.hk
  omega

theorem J_pos : 0 < D.J := by
  unfold J
  have := D.hj
  omega


end WinData

end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow
