import Dubon2026.SourceCellWindowBaseAngles

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData.Base
noncomputable section
open scoped Real
open Set

variable {D : WinData} (B : Base D)

theorem bottom_data {k₀ : Fin B.R.N} (h : k₀.val = 4) {za zb : ℂ} (hA : za ∈ B.R.arcSet k₀)
    (hB : zb ∈ B.R.arcSet k₀) (hstart : za ∈ segment ℝ (B.R.loop (B.R.φs k₀.castSucc)) zb) :
    za.im = D.Y₀ ∧ zb.im = D.Y₀ ∧ za.re ≤ zb.re := by
  rw [B.arc4 k₀ h, Set.mem_setOf_eq] at hA hB
  rw [B.brk4 k₀.castSucc h] at hstart
  have him : (⟨D.X₀, D.Y₀⟩ : ℂ).im = zb.im := hB.1.symm
  have hre : (⟨D.X₀, D.Y₀⟩ : ℂ).re ≤ zb.re := hB.2.1
  rw [segment_horizontal him hre, Set.mem_setOf_eq] at hstart
  exact ⟨hA.1, hB.1, hstart.2.2⟩

theorem top_data {k₀ : Fin B.R.N} (h : k₀.val = 1) {za zb : ℂ} (hA : za ∈ B.R.arcSet k₀)
    (hB : zb ∈ B.R.arcSet k₀) (hstart : za ∈ segment ℝ (B.R.loop (B.R.φs k₀.castSucc)) zb) :
    za.im = D.Y₁ ∧ zb.im = D.Y₁ ∧ zb.re ≤ za.re := by
  rw [B.arc1 k₀ h, Set.mem_setOf_eq] at hA hB
  rw [B.brk1 k₀.castSucc h, segment_symm ℝ] at hstart
  have him : zb.im = (⟨D.X₁, D.Y₁⟩ : ℂ).im := hB.1
  have hre : zb.re ≤ (⟨D.X₁, D.Y₁⟩ : ℂ).re := hB.2.2
  rw [segment_horizontal him hre, Set.mem_setOf_eq] at hstart
  exact ⟨hA.1, hB.1, hstart.2.1⟩

theorem left_data {k₀ : Fin B.R.N} (h23 : k₀.val = 2 ∨ k₀.val = 3) {za zb : ℂ}
    (hA : za ∈ B.R.arcSet k₀) (hB : zb ∈ B.R.arcSet k₀)
    (hstart : za ∈ segment ℝ (B.R.loop (B.R.φs k₀.castSucc)) zb) :
    za.re = D.X₀ ∧ zb.re = D.X₀ ∧ zb.im ≤ za.im := by
  rcases h23 with h | h
  · rw [B.arc2 k₀ h, Set.mem_setOf_eq] at hA hB
    rw [B.brk2 k₀.castSucc h, segment_symm ℝ] at hstart
    have hre : zb.re = (⟨D.X₀, D.Y₁⟩ : ℂ).re := hB.1
    have him : zb.im ≤ (⟨D.X₀, D.Y₁⟩ : ℂ).im := hB.2.2
    rw [segment_vertical hre him, Set.mem_setOf_eq] at hstart
    exact ⟨hA.1, hB.1, hstart.2.1⟩
  · rw [B.arc3 k₀ h, Set.mem_setOf_eq] at hA hB
    rw [B.brk3 k₀.castSucc h, segment_symm ℝ] at hstart
    have hre : zb.re = (⟨D.X₀, D.cy (D.jlo, D.klo)⟩ : ℂ).re := hB.1
    have him : zb.im ≤ (⟨D.X₀, D.cy (D.jlo, D.klo)⟩ : ℂ).im := hB.2.2
    rw [segment_vertical hre him, Set.mem_setOf_eq] at hstart
    exact ⟨hA.1, hB.1, hstart.2.1⟩

theorem right_data {k₀ : Fin B.R.N} (h05 : k₀.val = 0 ∨ k₀.val = 5) {za zb : ℂ}
    (hA : za ∈ B.R.arcSet k₀) (hB : zb ∈ B.R.arcSet k₀)
    (hstart : za ∈ segment ℝ (B.R.loop (B.R.φs k₀.castSucc)) zb) :
    za.re = D.X₁ ∧ zb.re = D.X₁ ∧ za.im ≤ zb.im := by
  rcases h05 with h | h
  · rw [B.arc0 k₀ h, Set.mem_setOf_eq] at hA hB
    rw [B.brk0 k₀.castSucc h] at hstart
    have hre : (⟨D.X₁, 0⟩ : ℂ).re = zb.re := hB.1.symm
    have him : (⟨D.X₁, 0⟩ : ℂ).im ≤ zb.im := hB.2.1
    rw [segment_vertical hre him, Set.mem_setOf_eq] at hstart
    exact ⟨hA.1, hB.1, hstart.2.2⟩
  · rw [B.arc5 k₀ h, Set.mem_setOf_eq] at hA hB
    rw [B.brk5 k₀.castSucc h] at hstart
    have hre : (⟨D.X₁, D.Y₀⟩ : ℂ).re = zb.re := hB.1.symm
    have him : (⟨D.X₁, D.Y₀⟩ : ℂ).im ≤ zb.im := hB.2.1
    rw [segment_vertical hre him, Set.mem_setOf_eq] at hstart
    exact ⟨hA.1, hB.1, hstart.2.2⟩

theorem right_range {k₀ : Fin B.R.N} (h05 : k₀.val = 0 ∨ k₀.val = 5) :
    B.R.arcIcc k₀ ⊆ Set.Ioo (-(π / 2)) (π / 2) ∨
      B.R.arcIcc k₀ ⊆ Set.Ioo (3 * π / 2) (5 * π / 2) := by
  have hπ := Real.pi_pos
  rcases h05 with h | h
  · left
    intro t ht
    have h' := B.rng0 k₀ h ht
    exact ⟨by linarith [h'.1], h'.2⟩
  · right
    intro t ht
    have h' := B.rng5 k₀ h ht
    exact ⟨h'.1, by linarith [h'.2]⟩

theorem val_cases (k₀ : Fin B.R.N) :
    (k₀.val = 0 ∨ k₀.val = 5) ∨ k₀.val = 1 ∨ (k₀.val = 2 ∨ k₀.val = 3) ∨ k₀.val = 4 := by
  have h := k₀.isLt
  have h6 := B.hN
  omega


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData.Base
