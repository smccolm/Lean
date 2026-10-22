import Dubon2026.SourceCellPlanarGridData

/-! DUB-17/18 -> original Abel-Jacobi -> actual paired cell dissection.
Use the exact six-arc square and refined-window outputs to identify the two
regions sharing each side, its orientation and C1 reversal, and the finite
intersection chains at every boundary point. These are the planar inputs
to pairing the constructed original-curve cells and to their Euler count.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
The existing rectangle and outer-window constructors provide the geometric
data; no new radial-region existence hypothesis is introduced by consumers.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
noncomputable section
open scoped Real
open Set

/-- Exact six-arc square geometry and strict center/split bounds. -/
def IsSquare (o hm : ℝ) (j k : ℤ) (c : ℂ) (yL : ℝ) (R : RadialRegion) : Prop :=
  ∃ (_hx₀ : o + j*hm < c.re) (_hx₁ : c.re < o + (j+1)*hm) (_hy₀ : o + k*hm < c.im) (_hy₁ : c.im < o + (k+1)*hm)
    (_hL₀ : o + k*hm < yL) (_hL₁ : yL < o + (k+1)*hm), PlanarRegions.RectClauses (o + j*hm) (o + (j+1)*hm) (o + k*hm) (o + (k+1)*hm) c yL R

/-- Closed segment on a prescribed vertical line. -/
def vseg (x lo hi : ℝ) : Set ℂ := {z : ℂ | z.re = x ∧ z.im ∈ Icc lo hi}

/-- Closed segment on a prescribed horizontal line. -/
def hseg (y lo hi : ℝ) : Set ℂ := {z : ℂ | z.im = y ∧ z.re ∈ Icc lo hi}

theorem mk_mem_vseg {x lo hi a b : ℝ} : (⟨a, b⟩ : ℂ) ∈ vseg x lo hi ↔ a = x ∧ lo ≤ b ∧ b ≤ hi :=
  Iff.rfl

theorem mk_mem_hseg {y lo hi a b : ℝ} : (⟨a, b⟩ : ℂ) ∈ hseg y lo hi ↔ b = y ∧ lo ≤ a ∧ a ≤ hi :=
  Iff.rfl

theorem vseg_eq_vseg {x lo hi x' lo' hi' : ℝ} (hlt : lo < hi) (h : vseg x lo hi = vseg x' lo' hi') :
    x = x' ∧ lo = lo' ∧ hi = hi' := by
  have h₁ : (⟨x, lo⟩ : ℂ) ∈ vseg x' lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨x, hi⟩ : ℂ) ∈ vseg x' lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, hlt.le, le_rfl⟩
  obtain ⟨e₁, e₂, e₃⟩ := mk_mem_vseg.1 h₁
  obtain ⟨-, -, e₅⟩ := mk_mem_vseg.1 h₂
  have hle' : lo' ≤ hi' := e₂.trans e₃
  have h₃ : (⟨x', lo'⟩ : ℂ) ∈ vseg x lo hi := by
    rw [h]; exact mk_mem_vseg.2 ⟨rfl, le_rfl, hle'⟩
  have h₄ : (⟨x', hi'⟩ : ℂ) ∈ vseg x lo hi := by
    rw [h]; exact mk_mem_vseg.2 ⟨rfl, hle', le_rfl⟩
  obtain ⟨-, e₆, -⟩ := mk_mem_vseg.1 h₃
  obtain ⟨-, -, e₇⟩ := mk_mem_vseg.1 h₄
  exact ⟨e₁, le_antisymm e₆ e₂, le_antisymm e₅ e₇⟩

theorem hseg_eq_hseg {y lo hi y' lo' hi' : ℝ} (hlt : lo < hi) (h : hseg y lo hi = hseg y' lo' hi') :
    y = y' ∧ lo = lo' ∧ hi = hi' := by
  have h₁ : (⟨lo, y⟩ : ℂ) ∈ hseg y' lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨hi, y⟩ : ℂ) ∈ hseg y' lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, hlt.le, le_rfl⟩
  obtain ⟨e₁, e₂, e₃⟩ := mk_mem_hseg.1 h₁
  obtain ⟨-, -, e₅⟩ := mk_mem_hseg.1 h₂
  have hle' : lo' ≤ hi' := e₂.trans e₃
  have h₃ : (⟨lo', y'⟩ : ℂ) ∈ hseg y lo hi := by
    rw [h]; exact mk_mem_hseg.2 ⟨rfl, le_rfl, hle'⟩
  have h₄ : (⟨hi', y'⟩ : ℂ) ∈ hseg y lo hi := by
    rw [h]; exact mk_mem_hseg.2 ⟨rfl, hle', le_rfl⟩
  obtain ⟨-, e₆, -⟩ := mk_mem_hseg.1 h₃
  obtain ⟨-, -, e₇⟩ := mk_mem_hseg.1 h₄
  exact ⟨e₁, le_antisymm e₆ e₂, le_antisymm e₅ e₇⟩

theorem vseg_ne_hseg {x lo hi y lo' hi' : ℝ} (hlt : lo < hi) : vseg x lo hi ≠ hseg y lo' hi' := by
  intro h
  have h₁ : (⟨x, lo⟩ : ℂ) ∈ hseg y lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨x, hi⟩ : ℂ) ∈ hseg y lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, hlt.le, le_rfl⟩
  exact hlt.ne ((mk_mem_hseg.1 h₁).1.trans (mk_mem_hseg.1 h₂).1.symm)

theorem hseg_ne_vseg {y lo hi x lo' hi' : ℝ} (hlt : lo < hi) : hseg y lo hi ≠ vseg x lo' hi' := by
  intro h
  have h₁ : (⟨lo, y⟩ : ℂ) ∈ vseg x lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨hi, y⟩ : ℂ) ∈ vseg x lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, hlt.le, le_rfl⟩
  exact hlt.ne ((mk_mem_vseg.1 h₁).1.trans (mk_mem_vseg.1 h₂).1.symm)

theorem eq_of_grid (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {s t : ℝ} (h : o + s * hm = o + t * hm) : s = t := by
  have h' : s * hm = t * hm := by linarith
  exact mul_right_cancel₀ hhm.ne' h'

theorem lt_of_grid (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {s t : ℝ} (h : o + s * hm < o + t * hm) : s < t := by
  have h' : s * hm < t * hm := by linarith
  exact lt_of_mul_lt_mul_right h' hhm.le

theorem int_eq_of_grid₀₀ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm = o + n * hm) :
    m = n := by
  exact_mod_cast eq_of_grid o hhm h

theorem int_eq_of_grid₀₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm = o + (n + 1) * hm) :
    m = n + 1 := by
  exact_mod_cast eq_of_grid o hhm h

theorem int_eq_of_grid₁₀ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + (m + 1) * hm = o + n * hm) :
    m + 1 = n := by
  exact_mod_cast eq_of_grid o hhm h

theorem int_eq_of_grid₁₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ)
    (h : o + (m + 1) * hm = o + (n + 1) * hm) : m = n := by
  have h' := eq_of_grid o hhm h
  have h'' : (m : ℝ) = n := by linarith
  exact_mod_cast h''

theorem int_lt_of_grid₀₀ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm < o + n * hm) :
    m < n := by
  exact_mod_cast lt_of_grid o hhm h

theorem int_lt_of_grid₀₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm < o + (n + 1) * hm) :
    m < n + 1 := by
  exact_mod_cast lt_of_grid o hhm h

theorem int_lt_of_grid₁₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ)
    (h : o + (m + 1) * hm < o + (n + 1) * hm) : m < n := by
  have h' := lt_of_grid o hhm h
  have h'' : (m : ℝ) < n := by linarith
  exact_mod_cast h''


end
end Dubon2026.SourceFunctionField.CellGeometry.SideIdentity
