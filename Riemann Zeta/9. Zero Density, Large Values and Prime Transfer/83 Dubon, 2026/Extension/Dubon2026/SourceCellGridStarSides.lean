import Dubon2026.SourceCellGridStarBounds

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
variable (M : GridData)

theorem right_arc₀₂ {j j' kk : ℤ} (hj : M.jlo ≤ j) (hj' : j' = j + 1) (a : Fin (M.base (j, kk)).N)
    (ha : a.val = 0) (a' : Fin (M.base (j', kk)).N) (ha' : a'.val = 2) :
    (M.base (j, kk)).arcSet a = (M.base (j', kk)).arcSet a' := by
  subst hj'
  exact SideIdentity.right_arcSet_eq₀₂ (isSquare_base M j kk) (isSquare_base M (j + 1) kk) (yL_succ M j kk hj) a ha a' ha'

theorem right_arc₅₃ {j j' kk : ℤ} (hj : M.jlo ≤ j) (hj' : j' = j + 1) (a : Fin (M.base (j, kk)).N)
    (ha : a.val = 5) (a' : Fin (M.base (j', kk)).N) (ha' : a'.val = 3) :
    (M.base (j, kk)).arcSet a = (M.base (j', kk)).arcSet a' := by
  subst hj'
  exact SideIdentity.right_arcSet_eq₅₃ (isSquare_base M j kk) (isSquare_base M (j + 1) kk) (yL_succ M j kk hj) a ha a' ha'

theorem upper_arc₁₄ {j kk kk' : ℤ} (hk' : kk' = kk + 1) (a : Fin (M.base (j, kk)).N) (ha : a.val = 1)
    (a' : Fin (M.base (j, kk')).N) (ha' : a'.val = 4) :
    (M.base (j, kk)).arcSet a = (M.base (j, kk')).arcSet a' := by
  subst hk'
  exact SideIdentity.upper_arcSet_eq₁₄ (isSquare_base M j kk) (isSquare_base M j (kk + 1)) a ha a' ha'

theorem right_of_eq {j j' kk kk' : ℤ} (hj : M.jlo ≤ j) (hj' : j' = j + 1) (hk' : kk' = kk)
    (a : Fin (M.base (j, kk)).N) (a' : Fin (M.base (j', kk')).N)
    (h : (M.base (j, kk)).arcSet a = (M.base (j', kk')).arcSet a') :
    (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  subst hj' hk'
  exact SideIdentity.right_of_arcSet_eq (isSquare_base M j _) (isSquare_base M (j + 1) _) (yL_succ M j _ hj) a a' h

theorem upper_of_eq {j j' kk kk' : ℤ} (hj' : j' = j) (hk' : kk' = kk + 1) (a : Fin (M.base (j, kk)).N)
    (a' : Fin (M.base (j', kk')).N) (h : (M.base (j, kk)).arcSet a = (M.base (j', kk')).arcSet a') :
    a.val = 1 ∧ a'.val = 4 := by
  subst hj' hk'
  exact SideIdentity.upper_of_arcSet_eq (isSquare_base M _ _) (isSquare_base M _ _) a a' h

theorem squares_of_arc {j kk : ℤ} (hj : M.jlo ≤ j) (a : Fin (M.base (j, kk)).N) {j'' kk'' : ℤ}
    (hj'' : M.jlo ≤ j'') (a'' : Fin (M.base (j'', kk'')).N)
    (h : (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a) :
    (j'' = j ∧ kk'' = kk) ∨ ((a.val = 0 ∨ a.val = 5) ∧ j'' = j + 1 ∧ kk'' = kk) ∨
      ((a.val = 2 ∨ a.val = 3) ∧ j'' = j - 1 ∧ kk'' = kk) ∨ (a.val = 1 ∧ j'' = j ∧ kk'' = kk + 1) ∨
      (a.val = 4 ∧ j'' = j ∧ kk'' = kk - 1) := by
  rcases SideIdentity.locality M.hhm (isSquare_base M j kk) (isSquare_base M j'' kk'') a a'' h.symm with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1, e2⟩
  · have h' := right_of_eq M hj e1 e2 a a'' h.symm
    omega
  · have h' := right_of_eq M hj'' e1 e2.symm a'' a h
    omega
  · have h' := upper_of_eq M e1 e2 a a'' h.symm
    omega
  · have h' := upper_of_eq M e1.symm e2 a'' a h
    omega

theorem win_cases (k₀ : Fin M.winReg.N) :
    (∃ i : ℤ, M.jlo ≤ i ∧ i ≤ M.jhi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.im = M.o + M.klo * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)}) ∨
    (∃ i : ℤ, M.jlo ≤ i ∧ i ≤ M.jhi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.im = M.o + (M.khi + 1) * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.cy (M.jlo, i)) (M.o + (i + 1) * M.hm)}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jlo, i))}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jhi, i))}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.cy (M.jhi, i)) (M.o + (i + 1) * M.hm)}) := by
  obtain ⟨-, -, -, -, -, hcases, -, -, -, -, -, -⟩ := M.winReg_spec
  rcases hcases k₀ with ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩ |
    ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩
  · exact Or.inl ⟨i, h1, h2, e⟩
  · exact Or.inr (Or.inl ⟨i, h1, h2, e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, h1, h2, e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1, h2, e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1, h2, e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, h1, h2, e⟩))))

theorem win_bottom (i : ℤ) (h1 : M.jlo ≤ i) (h2 : i ≤ M.jhi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.im = M.o + M.klo * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, hb, -, -, -, -, -⟩ := M.winReg_spec
  exact hb i h1 h2

theorem win_top (i : ℤ) (h1 : M.jlo ≤ i) (h2 : i ≤ M.jhi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.im = M.o + (M.khi + 1) * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, -, ht, -, -, -, -⟩ := M.winReg_spec
  exact ht i h1 h2

theorem win_leftUpper (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.cy (M.jlo, i)) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, -, -, hlu, -, -, -⟩ := M.winReg_spec
  exact hlu i h1 h2

theorem win_leftLower (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jlo, i))} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hll, -, -⟩ := M.winReg_spec
  exact hll i h1 h2

theorem win_rightLower (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jhi, i))} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrl, -⟩ := M.winReg_spec
  exact hrl i h1 h2

theorem win_rightUpper (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.cy (M.jhi, i)) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hru⟩ := M.winReg_spec
  exact hru i h1 h2

theorem sq_per {j kk : ℤ} (hj : M.jlo ≤ j) (hj2 : j ≤ M.jhi) (hk : M.klo ≤ kk) (hk2 : kk ≤ M.khi)
    (a : Fin (M.base (j, kk)).N) (k₀ : Fin M.winReg.N) (h : (M.base (j, kk)).arcSet a = M.winReg.arcSet k₀) :
    (a.val = 0 ∧ j = M.jhi) ∨ (a.val = 5 ∧ j = M.jhi) ∨ (a.val = 2 ∧ j = M.jlo) ∨ (a.val = 3 ∧ j = M.jlo) ∨
      (a.val = 4 ∧ kk = M.klo) ∨ (a.val = 1 ∧ kk = M.khi) := by
  rcases win_cases M k₀ with ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ |
    ⟨_i, -, -, e⟩
  · obtain ⟨-, e2, e3⟩ := SideIdentity.bottom_of_arcSet_eq M.hhm (isSquare_base M j kk) hk a (h.trans e)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e3, e2⟩))))
  · obtain ⟨-, e2, e3⟩ := SideIdentity.top_of_arcSet_eq M.hhm (isSquare_base M j kk) hk2 a (h.trans e)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e3, e2⟩))))
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.leftUpper_of_arcSet_eq M.hhm (isSquare_base M j kk) hj a (h.trans e)
    exact Or.inr (Or.inr (Or.inl ⟨e3, e1⟩))
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.leftLower_of_arcSet_eq M.hhm (isSquare_base M j kk) hj a (h.trans e)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e3, e1⟩)))
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.rightLower_of_arcSet_eq M.hhm (isSquare_base M j kk) hj2 a (h.trans e)
    exact Or.inr (Or.inl ⟨e3, e1⟩)
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.rightUpper_of_arcSet_eq M.hhm (isSquare_base M j kk) hj2 a (h.trans e)
    exact Or.inl ⟨e3, e1⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
