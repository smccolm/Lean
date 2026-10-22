import Dubon2026.SourceCellGridOuterSidePartner

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

theorem two_regions_some (j kk : ℤ) (Z : Set ℂ) (hsh : Shares M (some (j, kk)) Z) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ some (j, kk) ∧ Shares M ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' Z → ρ'' = some (j, kk) ∨ ρ'' = ρ' := by
  obtain ⟨hw, a, rfl⟩ := (shares_some_iff M (j, kk) Z).1 hsh
  obtain ⟨⟨hj, hj2⟩, hk, hk2⟩ := (mem_win_iff M).1 hw
  have hsquares : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a →
        M.jlo ≤ j'' ∧ j'' ≤ M.jhi ∧ M.klo ≤ kk'' ∧ kk'' ≤ M.khi ∧
        ((j'' = j ∧ kk'' = kk) ∨ ((a.val = 0 ∨ a.val = 5) ∧ j'' = j + 1 ∧ kk'' = kk) ∨
          ((a.val = 2 ∨ a.val = 3) ∧ j'' = j - 1 ∧ kk'' = kk) ∨ (a.val = 1 ∧ j'' = j ∧ kk'' = kk + 1) ∨
          (a.val = 4 ∧ j'' = j ∧ kk'' = kk - 1)) := by
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨hj'', hj''2⟩, hk'', hk''2⟩ := (mem_win_iff M).1 hw''
    exact ⟨hj'', hj''2, hk'', hk''2, squares_of_arc M hj a hj'' a'' ha''⟩
  have hperim := sq_per M hj hj2 hk hk2 a
  rcases (arcData_base M j kk).arcSet_cases a with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩
  ·
    by_cases hlt : j < M.jhi
    · obtain ⟨a', ha'⟩ := exists_idx M (j + 1, kk) 2 (by omega)
      refine two_of_square M a (j + 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₀₂ M hj rfl a h0 a' ha') ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jhi := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_rightUpper M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_rightUpper (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a h0).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : kk < M.khi
    · obtain ⟨a', ha'⟩ := exists_idx M (j, kk + 1) 4 (by omega)
      refine two_of_square M a j (kk + 1) ((mem_win_iff M).2 ⟨⟨hj, hj2⟩, by omega, by omega⟩)
        (Or.inr (by omega)) a' (upper_arc₁₄ M rfl a h1 a' ha') ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hkk : kk = M.khi := by omega
      subst hkk
      obtain ⟨k₀, hk₀⟩ := win_top M j hj hj2
      refine two_with_outside M a k₀ ((SideIdentity.arcSet_eq_top (isSquare_base M j M.khi) a h1).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : M.jlo < j
    · obtain ⟨a', ha'⟩ := exists_idx M (j - 1, kk) 0 (by omega)
      refine two_of_square M a (j - 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₀₂ M (by omega) (by omega) a' ha' a h2).symm ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jlo := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_leftUpper M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_leftUpper (isSquare_base M M.jlo kk) (yL_jlo M kk) a h2).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : M.jlo < j
    · obtain ⟨a', ha'⟩ := exists_idx M (j - 1, kk) 5 (by omega)
      refine two_of_square M a (j - 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₅₃ M (by omega) (by omega) a' ha' a h3).symm ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jlo := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_leftLower M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_leftLower (isSquare_base M M.jlo kk) (yL_jlo M kk) a h3).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : M.klo < kk
    · obtain ⟨a', ha'⟩ := exists_idx M (j, kk - 1) 1 (by omega)
      refine two_of_square M a j (kk - 1) ((mem_win_iff M).2 ⟨⟨hj, hj2⟩, by omega, by omega⟩)
        (Or.inr (by omega)) a' (upper_arc₁₄ M (by omega) a' ha' a h4).symm ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hkk : kk = M.klo := by omega
      subst hkk
      obtain ⟨k₀, hk₀⟩ := win_bottom M j hj hj2
      refine two_with_outside M a k₀ ((SideIdentity.arcSet_eq_bottom (isSquare_base M j M.klo) a h4).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : j < M.jhi
    · obtain ⟨a', ha'⟩ := exists_idx M (j + 1, kk) 3 (by omega)
      refine two_of_square M a (j + 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₅₃ M hj rfl a h5 a' ha') ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jhi := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_rightLower M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_rightLower (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a h5).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega

theorem two_regions : ∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares M ρ Z →
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares M ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ' := by
  intro ρ Z hsh
  rcases ρ with _ | ⟨j, kk⟩
  · exact two_regions_none M Z hsh
  · exact two_regions_some M j kk Z hsh


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
