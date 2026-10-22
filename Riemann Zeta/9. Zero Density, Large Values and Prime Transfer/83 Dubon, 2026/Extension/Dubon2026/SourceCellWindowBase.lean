import Dubon2026.SourceCellWindowAngles

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
noncomputable section
open scoped Real
open Set

variable (D : WinData)

/-- Constructed six-arc outer rectangle with exact source boundary data. -/
structure Base where
  /-- The constructed six-arc outer radial rectangle. -/
  R : RadialRegion
  hq : R.q = 0
  hN : R.N = 6
  hK : R.K = {z : ℂ | z.re ∈ Set.Icc D.X₀ D.X₁ ∧ z.im ∈ Set.Icc D.Y₀ D.Y₁}
  hKint : R.Kint = {z : ℂ | z.re ∈ Set.Ioo D.X₀ D.X₁ ∧ z.im ∈ Set.Ioo D.Y₀ D.Y₁}
  arc0 : ∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = D.X₁ ∧ z.im ∈ Set.Icc 0 D.Y₁}
  arc1 : ∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = D.Y₁ ∧ z.re ∈ Set.Icc D.X₀ D.X₁}
  arc2 : ∀ k : Fin R.N, k.val = 2 →
    R.arcSet k = {z : ℂ | z.re = D.X₀ ∧ z.im ∈ Set.Icc (D.cy (D.jlo, D.klo)) D.Y₁}
  arc3 : ∀ k : Fin R.N, k.val = 3 →
    R.arcSet k = {z : ℂ | z.re = D.X₀ ∧ z.im ∈ Set.Icc D.Y₀ (D.cy (D.jlo, D.klo))}
  arc4 : ∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = D.Y₀ ∧ z.re ∈ Set.Icc D.X₀ D.X₁}
  arc5 : ∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = D.X₁ ∧ z.im ∈ Set.Icc D.Y₀ 0}
  brk0 : ∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨D.X₁, 0⟩
  brk1 : ∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨D.X₁, D.Y₁⟩
  brk2 : ∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨D.X₀, D.Y₁⟩
  brk3 : ∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨D.X₀, D.cy (D.jlo, D.klo)⟩
  brk4 : ∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨D.X₀, D.Y₀⟩
  brk5 : ∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨D.X₁, D.Y₀⟩
  brk6 : ∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨D.X₁, 0⟩
  rad_right : ∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
    ∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / D.X₁)⁻¹
  rad_top : ∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / D.Y₁)⁻¹
  rad_left : ∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
    ∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / -D.X₀)⁻¹
  rad_bottom : ∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / -D.Y₀)⁻¹
  rng0 : ∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Set.Ico 0 (π / 2)
  rng1 : ∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Set.Ioo 0 π
  rng23 : ∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Set.Ioo (π / 2) (3 * π / 2)
  rng4 : ∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Set.Ioo π (2 * π)
  rng5 : ∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Set.Ioc (3 * π / 2) (2 * π)
  bdry : ∀ z ∈ R.K, z ∉ R.Kint → R.loop (ang z) = z
  seg : ∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
    R.loop '' Set.Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂)

theorem exists_base : Nonempty (Base D) := by
  have hsplit := D.cy_mem_Ioo D.jlo (Finset.mem_Icc.mpr ⟨le_refl D.klo, D.hk⟩)
  obtain ⟨R, hq, hN, hK, hKint, a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, b6,
      rr, rt, rl, rb, g0, g1, g23, g4, g5, hbd, hseg⟩ :=
    RectSixArcs.exists_rect_sixArcs D.X₀ D.X₁ D.Y₀ D.Y₁ (0 : ℂ) (D.cy (D.jlo, D.klo))
      (by rw [Complex.zero_re]; exact D.X₀_neg) (by rw [Complex.zero_re]; exact D.X₁_pos)
      (by rw [Complex.zero_im]; exact D.Y₀_neg) (by rw [Complex.zero_im]; exact D.Y₁_pos)
      hsplit.1 hsplit.2
  refine ⟨⟨R, hq, hN, hK, hKint, ?_, a1, a2, a3, a4, ?_, ?_, b1, b2, b3, b4, b5, ?_, ?_, ?_, ?_, ?_,
    g0, g1, g23, g4, g5, ?_, hseg⟩⟩
  · intro k hk
    have h := a0 k hk
    rw [Complex.zero_im] at h
    exact h
  · intro k hk
    have h := a5 k hk
    rw [Complex.zero_im] at h
    exact h
  · intro k hk
    have h := b0 k hk
    rw [Complex.zero_im] at h
    exact h
  · intro k hk
    have h := b6 k hk
    rw [Complex.zero_im] at h
    exact h
  · intro k hk t ht
    have h := rr k hk t ht
    rw [Complex.zero_re, sub_zero] at h
    exact h
  · intro k hk t ht
    have h := rt k hk t ht
    rw [Complex.zero_im, sub_zero] at h
    exact h
  · intro k hk t ht
    have h := rl k hk t ht
    rw [Complex.zero_re, zero_sub] at h
    exact h
  · intro k hk t ht
    have h := rb k hk t ht
    rw [Complex.zero_im, zero_sub] at h
    exact h
  · intro z hz hz'
    have h := hbd z hz hz'
    rw [sub_zero] at h
    exact h


end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow.WinData
