import Dubon2026.SourceCellGridIndexGeometry

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

theorem exists_centre (M : Finset ℂ) {o h : ℝ} (hh : 0 < h) (jhi : ℤ)
    (havoid : ∀ m ∈ M, ∀ j : ℤ, m.re - o ≠ j * h ∧ m.im - o ≠ j * h)
    (hsep : ∀ m ∈ M, ∀ m' ∈ M, m ≠ m' → ⌊(m.re - o) / h⌋ = ⌊(m'.re - o) / h⌋ →
      ⌊(m.im - o) / h⌋ = ⌊(m'.im - o) / h⌋ → False)
    (hcol : ∀ m ∈ M, ⌊(m.re - o) / h⌋ ≠ jhi) :
    ∃ centre : ℤ × ℤ → ℂ,
      (∀ p : ℤ × ℤ, (o + p.1 * h < (centre p).re ∧ (centre p).re < o + (p.1 + 1) * h) ∧
        (o + p.2 * h < (centre p).im ∧ (centre p).im < o + (p.2 + 1) * h)) ∧
      (∀ p : ℤ × ℤ, p.1 = jhi → o + p.2 * h < 0 → 0 < o + (p.2 + 1) * h → (centre p).im = 0) ∧
      (∀ m ∈ M, centre (⌊(m.re - o) / h⌋, ⌊(m.im - o) / h⌋) = m) := by
  have hpt : ∀ p : ℤ × ℤ, ∃ c : ℂ,
      ((o + p.1 * h < c.re ∧ c.re < o + (p.1 + 1) * h) ∧
        (o + p.2 * h < c.im ∧ c.im < o + (p.2 + 1) * h)) ∧
      (∀ m ∈ M, ⌊(m.re - o) / h⌋ = p.1 → ⌊(m.im - o) / h⌋ = p.2 → c = m) ∧
      ((∀ m ∈ M, ¬ (⌊(m.re - o) / h⌋ = p.1 ∧ ⌊(m.im - o) / h⌋ = p.2)) →
        o + p.2 * h < 0 → 0 < o + (p.2 + 1) * h → c.im = 0) := by
    intro p
    by_cases hex : ∃ m ∈ M, ⌊(m.re - o) / h⌋ = p.1 ∧ ⌊(m.im - o) / h⌋ = p.2
    · obtain ⟨m, hmM, hm1, hm2⟩ := hex
      refine ⟨m, inside_of_floor hh (havoid m hmM) p hm1 hm2, ?_, ?_⟩
      · intro m' hm'M hm'1 hm'2
        by_contra hne
        exact hsep m hmM m' hm'M hne (hm1.trans hm'1.symm) (hm2.trans hm'2.symm)
      · intro hnone
        exact ((hnone m hmM) ⟨hm1, hm2⟩).elim
    · by_cases hs : o + p.2 * h < 0 ∧ 0 < o + (p.2 + 1) * h
      · refine ⟨⟨o + (p.1 + 1 / 2) * h, 0⟩, ?_, ?_, ?_⟩
        · refine ⟨⟨?_, ?_⟩, hs.1, hs.2⟩
          · show o + p.1 * h < o + (p.1 + 1 / 2) * h
            nlinarith
          · show o + (p.1 + 1 / 2) * h < o + (p.1 + 1) * h
            nlinarith
        · intro m hmM hm1 hm2
          exact (hex ⟨m, hmM, hm1, hm2⟩).elim
        · intro _ _ _
          rfl
      · refine ⟨⟨o + (p.1 + 1 / 2) * h, o + (p.2 + 1 / 2) * h⟩, ?_, ?_, ?_⟩
        · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
          · show o + p.1 * h < o + (p.1 + 1 / 2) * h
            nlinarith
          · show o + (p.1 + 1 / 2) * h < o + (p.1 + 1) * h
            nlinarith
          · show o + p.2 * h < o + (p.2 + 1 / 2) * h
            nlinarith
          · show o + (p.2 + 1 / 2) * h < o + (p.2 + 1) * h
            nlinarith
        · intro m hmM hm1 hm2
          exact (hex ⟨m, hmM, hm1, hm2⟩).elim
        · intro _ hs1 hs2
          exact (hs ⟨hs1, hs2⟩).elim
  choose centre hc using hpt
  refine ⟨centre, fun p => (hc p).1, ?_, ?_⟩
  · intro p hp1 hs1 hs2
    refine (hc p).2.2 ?_ hs1 hs2
    intro m hmM hm
    exact hcol m hmM (hm.1.trans hp1)
  · intro m hmM
    exact (hc (⌊(m.re - o) / h⌋, ⌊(m.im - o) / h⌋)).2.1 m hmM rfl rfl

theorem exists_capAt (Bad : Finset ℂ) (o h : ℝ)
    (hsep : ∀ b ∈ Bad, ∀ b' ∈ Bad, b ≠ b' → ⌊(b.re - o) / h⌋ = ⌊(b'.re - o) / h⌋ →
      ⌊(b.im - o) / h⌋ = ⌊(b'.im - o) / h⌋ → False) :
    ∃ capAt : ℤ × ℤ → Option ℂ, ∀ (p : ℤ × ℤ) (b : ℂ), capAt p = some b ↔
      b ∈ Bad ∧ ⌊(b.re - o) / h⌋ = p.1 ∧ ⌊(b.im - o) / h⌋ = p.2 := by
  have hpt : ∀ p : ℤ × ℤ, ∃ c : Option ℂ, ∀ b : ℂ, c = some b ↔
      b ∈ Bad ∧ ⌊(b.re - o) / h⌋ = p.1 ∧ ⌊(b.im - o) / h⌋ = p.2 := by
    intro p
    by_cases hex : ∃ b ∈ Bad, ⌊(b.re - o) / h⌋ = p.1 ∧ ⌊(b.im - o) / h⌋ = p.2
    · obtain ⟨b₀, hb₀, h₀1, h₀2⟩ := hex
      refine ⟨some b₀, fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
      · obtain rfl := Option.some.inj hb
        exact ⟨hb₀, h₀1, h₀2⟩
      · by_cases hbb : b₀ = b
        · rw [hbb]
        · exact (hsep b₀ hb₀ b hb.1 hbb (h₀1.trans hb.2.1.symm) (h₀2.trans hb.2.2.symm)).elim
    · refine ⟨none, fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
      · cases hb
      · exact (hex ⟨b, hb⟩).elim
  choose capAt hcap using hpt
  exact ⟨capAt, hcap⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
