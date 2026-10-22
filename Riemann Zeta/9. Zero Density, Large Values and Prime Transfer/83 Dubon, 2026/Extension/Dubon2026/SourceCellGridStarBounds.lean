import Dubon2026.SourceCellSideRealization

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
namespace Dubon2026.SourceFunctionField.CellGeometry.StarProperty
noncomputable section
open scoped Real
open Set

open PlanarRegions

theorem le_of_grid {o hm : ℝ} (hhm : 0 < hm) {s t : ℝ} (h : o + s * hm ≤ o + t * hm) : s ≤ t := by
  by_contra hc
  have h' := mul_lt_mul_of_pos_right (not_le.mp hc) hhm
  linarith

theorem int_le_of_grid₀₀ {o hm : ℝ} (hhm : 0 < hm) {m n : ℤ} (h : o + m * hm ≤ o + n * hm) : m ≤ n := by
  exact_mod_cast le_of_grid hhm h

theorem int_le_of_grid₀₁ {o hm : ℝ} (hhm : 0 < hm) {m n : ℤ} (h : o + m * hm ≤ o + (n + 1) * hm) :
    m ≤ n + 1 := by
  exact_mod_cast le_of_grid hhm h

theorem int_le_of_grid₁₁ {o hm : ℝ} (hhm : 0 < hm) {m n : ℤ} (h : o + (m + 1) * hm ≤ o + (n + 1) * hm) :
    m ≤ n := by
  have h' := le_of_grid hhm h
  have h'' : (m : ℝ) ≤ n := by linarith
  exact_mod_cast h''

theorem mem_vseg {x lo hi : ℝ} {z : ℂ} : z ∈ SideIdentity.vseg x lo hi ↔ z.re = x ∧ lo ≤ z.im ∧ z.im ≤ hi :=
  Iff.rfl

theorem mem_hseg {y lo hi : ℝ} {z : ℂ} : z ∈ SideIdentity.hseg y lo hi ↔ z.im = y ∧ lo ≤ z.re ∧ z.re ≤ hi :=
  Iff.rfl

theorem some_mk_eq {j kk j' kk' : ℤ} (h1 : j = j') (h2 : kk = kk') :
    (some (j, kk) : Option (ℤ × ℤ)) = some (j', kk') := by
  rw [h1, h2]

theorem some_mk_ne {j kk j' kk' : ℤ} (h : j ≠ j' ∨ kk ≠ kk') :
    (some (j, kk) : Option (ℤ × ℤ)) ≠ some (j', kk') := by
  intro e
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e)
  rcases h with h | h
  · exact h e1
  · exact h e2

open PlanarRegions
variable (M : GridData)

theorem mem_win_iff {j kk : ℤ} :
    (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ↔ (M.jlo ≤ j ∧ j ≤ M.jhi) ∧ (M.klo ≤ kk ∧ kk ≤ M.khi) :=
  Iff.rfl

theorem cy_eq (j kk : ℤ) : (M.ctr (j, kk)).im = M.cy (j, kk) := rfl

theorem yL_jlo (kk : ℤ) : M.yL (M.jlo, kk) = M.cy (M.jlo, kk) := by
  show (if M.jlo = M.jlo then (M.ctr (M.jlo, kk)).im else (M.ctr (M.jlo - 1, kk)).im) = (M.ctr (M.jlo, kk)).im
  exact if_pos rfl

theorem yL_succ (j kk : ℤ) (hj : M.jlo ≤ j) : M.yL (j + 1, kk) = (M.ctr (j, kk)).im := by
  have h : ¬ (j + 1 = M.jlo) := by omega
  have e : j + 1 - 1 = j := by omega
  show (if j + 1 = M.jlo then (M.ctr (j + 1, kk)).im else (M.ctr (j + 1 - 1, kk)).im) = (M.ctr (j, kk)).im
  rw [if_neg h, e]

theorem isSquare_base (j kk : ℤ) :
    SideIdentity.IsSquare M.o M.hm j kk (M.ctr (j, kk)) (M.yL (j, kk)) (M.base (j, kk)) :=
  ⟨(M.ctr_mem (j, kk)).1.1, (M.ctr_mem (j, kk)).1.2, (M.ctr_mem (j, kk)).2.1, (M.ctr_mem (j, kk)).2.2,
    (M.yL_mem (j, kk)).1, (M.yL_mem (j, kk)).2, M.base_spec (j, kk)⟩

theorem arcData_base (j kk : ℤ) :
    SideIdentity.ArcData (M.base (j, kk)) (M.o + j * M.hm) (M.o + (j + 1) * M.hm) (M.o + kk * M.hm)
      (M.o + (kk + 1) * M.hm) (M.ctr (j, kk)).im (M.yL (j, kk)) :=
  SideIdentity.arcData_of_isSquare (isSquare_base M j kk)

theorem exists_idx (p : ℤ × ℤ) (n : ℕ) (hn : n < 6) : ∃ a : Fin (M.base p).N, a.val = n := by
  have hN := M.base_N p
  exact ⟨⟨n, by omega⟩, rfl⟩

theorem of_mem_baseK {j kk : ℤ} {v : ℂ} (h : v ∈ (M.base (j, kk)).K) :
    (M.o + j * M.hm ≤ v.re ∧ v.re ≤ M.o + (j + 1) * M.hm) ∧
      (M.o + kk * M.hm ≤ v.im ∧ v.im ≤ M.o + (kk + 1) * M.hm) := by
  rw [(M.base_spec (j, kk)).2.2.1] at h
  exact h

theorem mem_baseK_of {j kk : ℤ} {v : ℂ} (h1 : M.o + j * M.hm ≤ v.re) (h2 : v.re ≤ M.o + (j + 1) * M.hm)
    (h3 : M.o + kk * M.hm ≤ v.im) (h4 : v.im ≤ M.o + (kk + 1) * M.hm) : v ∈ (M.base (j, kk)).K := by
  rw [(M.base_spec (j, kk)).2.2.1]
  exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem not_mem_winKint {v : ℂ} (h : v ∉ M.winReg.Kint) :
    v.re ≤ M.o + M.jlo * M.hm ∨ M.o + (M.jhi + 1) * M.hm ≤ v.re ∨
      v.im ≤ M.o + M.klo * M.hm ∨ M.o + (M.khi + 1) * M.hm ≤ v.im := by
  by_cases h1 : v.re ≤ M.o + M.jlo * M.hm
  · exact Or.inl h1
  by_cases h2 : M.o + (M.jhi + 1) * M.hm ≤ v.re
  · exact Or.inr (Or.inl h2)
  by_cases h3 : v.im ≤ M.o + M.klo * M.hm
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : M.o + (M.khi + 1) * M.hm ≤ v.im
  · exact Or.inr (Or.inr (Or.inr h4))
  exfalso
  apply h
  rw [M.winReg_Kint]
  exact ⟨⟨not_le.mp h1, not_le.mp h2⟩, not_le.mp h3, not_le.mp h4⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
