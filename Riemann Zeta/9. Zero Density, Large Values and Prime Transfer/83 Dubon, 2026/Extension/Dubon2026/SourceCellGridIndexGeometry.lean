import Dubon2026.SourceCellGridWindow

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

theorem dist_mid_le {o h : ℝ} {j k : ℤ} {z : ℂ} (hz : z ∈ gridSquare o h j k) :
    dist z ⟨o + (j + 1 / 2) * h, o + (k + 1 / 2) * h⟩ ≤ h := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hz
  rw [Complex.dist_eq]
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  have hre : (z - ⟨o + (j + 1 / 2) * h, o + (k + 1 / 2) * h⟩ : ℂ).re = z.re - (o + (j + 1 / 2) * h) :=
    rfl
  have him : (z - ⟨o + (j + 1 / 2) * h, o + (k + 1 / 2) * h⟩ : ℂ).im = z.im - (o + (k + 1 / 2) * h) :=
    rfl
  rw [hre, him]
  have h1 : |z.re - (o + (j + 1 / 2) * h)| ≤ h / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h2 : |z.im - (o + (k + 1 / 2) * h)| ≤ h / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

open Complex in


theorem inside_of_floor {o h : ℝ} (hh : 0 < h) {m : ℂ}
    (havoid : ∀ j : ℤ, m.re - o ≠ j * h ∧ m.im - o ≠ j * h) (p : ℤ × ℤ)
    (h1 : ⌊(m.re - o) / h⌋ = p.1) (h2 : ⌊(m.im - o) / h⌋ = p.2) :
    (o + p.1 * h < m.re ∧ m.re < o + (p.1 + 1) * h) ∧ (o + p.2 * h < m.im ∧ m.im < o + (p.2 + 1) * h) := by
  have key : ∀ (y : ℝ) (q : ℤ), (∀ j : ℤ, y - o ≠ j * h) → ⌊(y - o) / h⌋ = q →
      o + q * h < y ∧ y < o + (q + 1) * h := by
    intro y q hav hq
    have hle : (q : ℝ) * h ≤ y - o := by
      have h0 := Int.floor_le ((y - o) / h)
      rw [hq] at h0
      exact (le_div_iff₀ hh).mp h0
    have hlt : y - o < (q + 1) * h := by
      have h0 := Int.lt_floor_add_one ((y - o) / h)
      rw [hq] at h0
      exact (div_lt_iff₀ hh).mp h0
    have hne : y - o ≠ q * h := hav q
    constructor
    · exact lt_of_le_of_ne (by linarith) (fun heq => hne (by linarith))
    · linarith
  exact ⟨key m.re p.1 (fun j => (havoid j).1) h1, key m.im p.2 (fun j => (havoid j).2) h2⟩

theorem floor_eq_of_mem {o h : ℝ} (hh : 0 < h) {b : ℂ}
    (havoid : ∀ j : ℤ, b.re - o ≠ j * h ∧ b.im - o ≠ j * h) {j k : ℤ} (hb : b ∈ gridSquare o h j k) :
    ⌊(b.re - o) / h⌋ = j ∧ ⌊(b.im - o) / h⌋ = k := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := hb
  have key : ∀ (y : ℝ) (q : ℤ), o + q * h ≤ y → y ≤ o + (q + 1) * h →
      y - o ≠ ((q + 1 : ℤ) : ℝ) * h → ⌊(y - o) / h⌋ = q := by
    intro y q hy1 hy2 hne
    rw [Int.floor_eq_iff]
    push_cast at hne
    constructor
    · rw [le_div_iff₀ hh]
      linarith
    · rw [div_lt_iff₀ hh]
      exact lt_of_le_of_ne (by linarith) hne
  exact ⟨key b.re j hr1 hr2 (havoid (j + 1)).1, key b.im k hi1 hi2 (havoid (k + 1)).2⟩


theorem floor_gap {x y o h : ℝ} (hh : 0 < h) (hgap : 3 * h ≤ x - y) :
    2 ≤ ⌊(x - o) / h⌋ - ⌊(y - o) / h⌋ := by
  have hu : (x - o) / h - 1 < ⌊(x - o) / h⌋ := Int.sub_one_lt_floor _
  have hv : (⌊(y - o) / h⌋ : ℝ) ≤ (y - o) / h := Int.floor_le _
  have hd : (2 : ℝ) < (⌊(x - o) / h⌋ : ℝ) - (⌊(y - o) / h⌋ : ℝ) := by
    have h3 : (3 : ℝ) ≤ (x - y) / h := by
      rw [le_div_iff₀ hh]
      linarith
    have h4 : (x - o) / h - (y - o) / h = (x - y) / h := by
      field_simp
      ring
    nlinarith [h3, h4]
  have : (2 : ℤ) < ⌊(x - o) / h⌋ - ⌊(y - o) / h⌋ := by exact_mod_cast hd
  omega

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
