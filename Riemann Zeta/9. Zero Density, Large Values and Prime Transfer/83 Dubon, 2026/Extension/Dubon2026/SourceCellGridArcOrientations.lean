import Dubon2026.SourceCellGridArcClassification

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
namespace Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
noncomputable section
open scoped Real
open Set

open PlanarRegions
variable (M : GridData)

/-- Orientation of a square boundary side. -/
def sqbit (p : ℤ × ℤ) (k : Fin (M.base p).N) : Bool := decide (k.val = 0 ∨ k.val = 1 ∨ k.val = 5)

open scoped Classical in

/-- Opposite orientation on a matching outer-window side. -/
noncomputable def perbit (k₀ : Fin M.winReg.N) : Bool :=
  decide ((∃ j : ℤ, M.winReg.arcSet k₀ =
      {z : ℂ | z.im = M.o + M.klo * M.hm ∧ z.re ∈ Icc (M.o + j * M.hm) (M.o + (j + 1) * M.hm)}) ∨
    (∃ k : ℤ, M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.cy (M.jlo, k)) (M.o + (k + 1) * M.hm)}) ∨
    (∃ k : ℤ, M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.o + k * M.hm) (M.cy (M.jlo, k))}))

theorem idx_of_perbit {p : ℤ × ℤ} (hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (k : Fin (M.base p).N) {k₀ : Fin M.winReg.N} (heq : (M.base p).arcSet k = M.winReg.arcSet k₀)
    (hb : perbit M k₀ = true) : k.val = 2 ∨ k.val = 3 ∨ k.val = 4 := by
  simp only [perbit, decide_eq_true_eq] at hb
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  rcases hb with ⟨j, hset⟩ | ⟨k₁, hset⟩ | ⟨k₁, hset⟩
  · exact Or.inr (Or.inr
      (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2)
  · exact Or.inl
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
  · exact Or.inr (Or.inl
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1)

theorem perbit_eq_false_of_pos {p : ℤ × ℤ} (hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (k : Fin (M.base p).N) {k₀ : Fin M.winReg.N} (heq : (M.base p).arcSet k = M.winReg.arcSet k₀)
    (hpos : k.val = 0 ∨ k.val = 1 ∨ k.val = 5) : perbit M k₀ = false := by
  cases h : perbit M k₀
  · rfl
  · exact absurd (idx_of_perbit M hp k heq h) (by omega)

theorem bit_sq_sq : ∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
    (M.base p).arcSet k = (M.base p').arcSet k' → sqbit M p' k' = !sqbit M p k := by
  intro p p' hne k k' heq
  rcases pair_of_arcSet_eq M.hhm (isSquare_base M p) (isSquare_base M p') (fst_ne_or_snd_ne hne)
      k k' heq with ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ <;>
    simp [sqbit, hk, hk']

theorem bit_sq_per : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
    (M.base p).arcSet k = M.winReg.arcSet k₀ → perbit M k₀ = !sqbit M p k := by
  intro p k k₀ hp heq
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  obtain ⟨-, -, -, -, -, hsix, -⟩ := M.winReg_spec
  rcases hsix k₀ with ⟨j, -, -, hset, -⟩ | ⟨j, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩ |
    ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩
  · have h4 := (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2
    have hb : perbit M k₀ = true := by
      simp only [perbit, decide_eq_true_eq]
      exact Or.inl ⟨j, hset⟩
    simp [sqbit, hb, h4]
  · have h1 := (SideIdentity.top_of_arcSet_eq M.hhm hsq (J := j) (K := M.khi) hpk.2 k (heq.trans hset)).2.2
    have hb := perbit_eq_false_of_pos M hp k heq (Or.inr (Or.inl h1))
    simp [sqbit, hb, h1]
  · have h2 :=
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hb : perbit M k₀ = true := by
      simp only [perbit, decide_eq_true_eq]
      exact Or.inr (Or.inl ⟨k₁, hset⟩)
    simp [sqbit, hb, h2]
  · have h3 :=
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hb : perbit M k₀ = true := by
      simp only [perbit, decide_eq_true_eq]
      exact Or.inr (Or.inr ⟨k₁, hset⟩)
    simp [sqbit, hb, h3]
  · have h5 :=
      (SideIdentity.rightLower_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hb := perbit_eq_false_of_pos M hp k heq (Or.inr (Or.inr h5))
    simp [sqbit, hb, h5]
  · have h0 :=
      (SideIdentity.rightUpper_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hb := perbit_eq_false_of_pos M hp k heq (Or.inl h0)
    simp [sqbit, hb, h0]


end
end Dubon2026.SourceFunctionField.CellGeometry.ArcReversal
