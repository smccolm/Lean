import Dubon2026.SourceCellGridStarRelations

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

theorem two_regions_none (Z : Set ℂ) (hsh : Shares M none Z) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ none ∧ Shares M ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' Z → ρ'' = none ∨ ρ'' = ρ' := by
  obtain ⟨k₀, rfl⟩ := (shares_none_iff M Z).1 hsh
  have hjj := M.hjlt
  have hkk := M.hklt
  rcases win_cases M k₀ with ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩ |
    ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_bottom (isSquare_base M i M.klo)
    refine ⟨some (i, M.klo), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨h1, h2⟩, le_rfl, by omega⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ i M.klo ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨-, hk'', -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -⟩ := SideIdentity.bottom_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hk'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_top (isSquare_base M i M.khi)
    refine ⟨some (i, M.khi), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨h1, h2⟩, by omega, le_rfl⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ i M.khi ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨-, -, hk''⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -⟩ := SideIdentity.top_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hk'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_leftUpper (isSquare_base M M.jlo i) (yL_jlo M i)
    refine ⟨some (M.jlo, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨le_rfl, by omega⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jlo i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨hj'', -⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.leftUpper_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_leftLower (isSquare_base M M.jlo i) (yL_jlo M i)
    refine ⟨some (M.jlo, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨le_rfl, by omega⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jlo i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨hj'', -⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.leftLower_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_rightLower (isSquare_base M M.jhi i) (cy_eq M M.jhi i)
    refine ⟨some (M.jhi, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨by omega, le_rfl⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jhi i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨-, hj''⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.rightLower_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_rightUpper (isSquare_base M M.jhi i) (cy_eq M M.jhi i)
    refine ⟨some (M.jhi, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨by omega, le_rfl⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jhi i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨-, hj''⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.rightUpper_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
