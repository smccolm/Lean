import Dubon2026.SourceCellGridVertexCounts

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
namespace Dubon2026.SourceFunctionField.CellGeometry.GridVertices
noncomputable section
open scoped Real
open Set

variable {o hm : ℝ} {jlo jhi klo khi : ℤ} {ctr : ℤ × ℤ → ℂ}

/-- The six-arc rectangle endpoint identities. -/
structure BreakData (R : RadialRegion) (x₀ x₁ y₀ y₁ yc ys : ℝ) : Prop where
  hN : R.N = 6
  b0 : ∀ i : Fin (R.N + 1), i.val = 0 → R.loop (R.φs i) = ⟨x₁, yc⟩
  b1 : ∀ i : Fin (R.N + 1), i.val = 1 → R.loop (R.φs i) = ⟨x₁, y₁⟩
  b2 : ∀ i : Fin (R.N + 1), i.val = 2 → R.loop (R.φs i) = ⟨x₀, y₁⟩
  b3 : ∀ i : Fin (R.N + 1), i.val = 3 → R.loop (R.φs i) = ⟨x₀, ys⟩
  b4 : ∀ i : Fin (R.N + 1), i.val = 4 → R.loop (R.φs i) = ⟨x₀, y₀⟩
  b5 : ∀ i : Fin (R.N + 1), i.val = 5 → R.loop (R.φs i) = ⟨x₁, y₀⟩
  b6 : ∀ i : Fin (R.N + 1), i.val = 6 → R.loop (R.φs i) = ⟨x₁, yc⟩

theorem breakData_of_rectClauses {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {ys : ℝ} {R : RadialRegion}
    (h : PlanarRegions.RectClauses x₀ x₁ y₀ y₁ p ys R) : BreakData R x₀ x₁ y₀ y₁ p.im ys := by
  obtain ⟨-, hN, -, -, -, -, -, -, -, -, b0, b1, b2, b3, b4, b5, b6, -⟩ := h
  exact ⟨hN, b0, b1, b2, b3, b4, b5, b6⟩

theorem rect_break_mem_of (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi)
    {R : RadialRegion}
    (h : PlanarRegions.RectClauses (o + j * hm) (o + (j + 1) * hm) (o + k * hm) (o + (k + 1) * hm) (ctr (j, k))
      (yL jlo ctr (j, k)) R)
    (i : Fin (R.N + 1)) : R.loop (R.φs i) ∈ B₀ o hm jlo jhi klo khi ctr := by
  have D := breakData_of_rectClauses h
  have hN := D.hN
  have hi := i.isLt
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6) with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [D.b0 i h0]
    exact right_mem_B₀ j k hj₁ hj₂ hk₁ hk₂
  · rw [D.b1 i h1]
    exact corner_mem_B₀ (j + 1) (k + 1) (by omega) (by omega) (by omega) (by omega)
      (by push_cast; ring) (by push_cast; ring)
  · rw [D.b2 i h2]
    exact corner_mem_B₀ j (k + 1) (by omega) (by omega) (by omega) (by omega) rfl (by push_cast; ring)
  · rw [D.b3 i h3]
    by_cases hj : j = jlo
    · rw [yL_of_eq hj k, hj]
      exact left_mem_B₀ k hk₁ hk₂
    · rw [yL_of_ne hj k]
      exact right_mem_B₀_of_eq (j - 1) k (by omega) (by omega) hk₁ hk₂ (by push_cast; ring)
  · rw [D.b4 i h4]
    exact corner_mem_B₀ j k (by omega) (by omega) (by omega) (by omega) rfl rfl
  · rw [D.b5 i h5]
    exact corner_mem_B₀ (j + 1) k (by omega) (by omega) (by omega) (by omega) (by push_cast; ring) rfl
  · rw [D.b6 i h6]
    exact right_mem_B₀ j k hj₁ hj₂ hk₁ hk₂

theorem rect_break_mem (p : ℤ × ℤ) (hp₁ : jlo ≤ p.1) (hp₂ : p.1 ≤ jhi) (hp₃ : klo ≤ p.2) (hp₄ : p.2 ≤ khi)
    {R : RadialRegion}
    (h : PlanarRegions.RectClauses (o + p.1 * hm) (o + (p.1 + 1) * hm) (o + p.2 * hm) (o + (p.2 + 1) * hm) (ctr p)
      (yL jlo ctr p) R)
    (i : Fin (R.N + 1)) : R.loop (R.φs i) ∈ B₀ o hm jlo jhi klo khi ctr := by
  obtain ⟨j, k⟩ := p
  exact rect_break_mem_of j k hp₁ hp₂ hp₃ hp₄ h i

theorem window_break_mem {hj : jlo ≤ jhi} {hk : klo ≤ khi}
    {R : RadialRegion}
    (hW : PlanarRegions.WindowClauses o hm jlo jhi klo khi (fun p => (ctr p).im) R)
    (k : Fin R.N) :
    R.loop (R.φs k.castSucc) ∈ B₀ o hm jlo jhi klo khi ctr ∧
      R.loop (R.φs k.succ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  obtain ⟨-, -, -, -, -, harc, -⟩ := hW
  rcases harc k with ⟨j, hj₁, hj₂, -, e₁, e₂, -⟩ | ⟨j, hj₁, hj₂, -, e₁, e₂, -⟩ |
    ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩ | ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩ | ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩ |
    ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩
  ·
    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ j klo (by omega) (by omega) (by omega) (by omega) rfl rfl,
      corner_mem_B₀ (j + 1) klo (by omega) (by omega) (by omega) (by omega) (by push_cast; ring) rfl⟩
  ·
    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ (j + 1) (khi + 1) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring) (by push_cast; ring),
      corner_mem_B₀ j (khi + 1) (by omega) (by omega) (by omega) (by omega) rfl (by push_cast; ring)⟩
  ·
    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ jlo (k₀ + 1) (by omega) (by omega) (by omega) (by omega) rfl (by push_cast; ring),
      left_mem_B₀ k₀ hk₁ hk₂⟩
  ·
    rw [e₁, e₂]
    exact ⟨left_mem_B₀ k₀ hk₁ hk₂,
      corner_mem_B₀ jlo k₀ (by omega) (by omega) (by omega) (by omega) rfl rfl⟩
  ·

    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ (jhi + 1) k₀ (by omega) (by omega) (by omega) (by omega) (by push_cast; ring) rfl,
      right_mem_B₀ jhi k₀ hj le_rfl hk₁ hk₂⟩
  ·
    rw [e₁, e₂]
    exact ⟨right_mem_B₀ jhi k₀ hj le_rfl hk₁ hk₂,
      corner_mem_B₀ (jhi + 1) (k₀ + 1) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring) (by push_cast; ring)⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.GridVertices
