import Dubon2026.SourceCellGridAdjacentExterior

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

theorem horiz_chain {j j' kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j', kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j', kk)).K) : Relation.ReflTransGen (Adj M v) (some (j, kk)) (some (j', kk)) := by
  obtain ⟨⟨r1, r2⟩, -⟩ := of_mem_baseK M hv
  obtain ⟨⟨r1', r2'⟩, -⟩ := of_mem_baseK M hv'
  have b1 : j ≤ j' + 1 := int_le_of_grid₀₁ M.hhm (r1.trans r2')
  have b2 : j' ≤ j + 1 := int_le_of_grid₀₁ M.hhm (r1'.trans r2)
  have h3 : j' = j ∨ j' = j + 1 ∨ j = j' + 1 := by omega
  rcases h3 with e | e | e
  · subst e
    exact Relation.ReflTransGen.refl
  · subst e
    exact Relation.ReflTransGen.single (adj_right M hw hw' hv hv')
  · subst e
    exact Relation.ReflTransGen.single (adj_symm M (adj_right M hw' hw hv' hv))

theorem vert_chain {j kk kk' : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j, kk') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j, kk')).K) : Relation.ReflTransGen (Adj M v) (some (j, kk)) (some (j, kk')) := by
  obtain ⟨-, i1, i2⟩ := of_mem_baseK M hv
  obtain ⟨-, i1', i2'⟩ := of_mem_baseK M hv'
  have b1 : kk ≤ kk' + 1 := int_le_of_grid₀₁ M.hhm (i1.trans i2')
  have b2 : kk' ≤ kk + 1 := int_le_of_grid₀₁ M.hhm (i1'.trans i2)
  have h3 : kk' = kk ∨ kk' = kk + 1 ∨ kk = kk' + 1 := by omega
  rcases h3 with e | e | e
  · subst e
    exact Relation.ReflTransGen.refl
  · subst e
    exact Relation.ReflTransGen.single (adj_upper M hw hw' hv hv')
  · subst e
    exact Relation.ReflTransGen.single (adj_symm M (adj_upper M hw' hw hv' hv))

theorem sq_chain {j kk j' kk' : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j', kk') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j', kk')).K) : Relation.ReflTransGen (Adj M v) (some (j, kk)) (some (j', kk')) := by
  obtain ⟨-, hk, hk2⟩ := (mem_win_iff M).1 hw
  obtain ⟨⟨hj', hj'2⟩, -⟩ := (mem_win_iff M).1 hw'
  obtain ⟨-, i1, i2⟩ := of_mem_baseK M hv
  obtain ⟨⟨r1', r2'⟩, -⟩ := of_mem_baseK M hv'
  have hwm : (j', kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := (mem_win_iff M).2 ⟨⟨hj', hj'2⟩, hk, hk2⟩
  have hvm : v ∈ (M.base (j', kk)).K := mem_baseK_of M r1' r2' i1 i2
  exact (horiz_chain M hw hwm hv hvm).trans (vert_chain M hwm hw' hvm hv')

theorem star : ∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains M ρ v → Contains M ρ' v →
    Relation.ReflTransGen (Adj M v) ρ ρ' := by
  intro v ρ ρ' h h'
  rcases ρ with _ | ⟨j, kk⟩
  · rcases ρ' with _ | ⟨j', kk'⟩
    · exact Relation.ReflTransGen.refl
    · obtain ⟨hw', hv'⟩ := (contains_some_iff M _ _).1 h'
      exact Relation.ReflTransGen.single (adj_symm M (adj_outside M hw' hv' ((contains_none_iff M _).1 h)))
  · obtain ⟨hw, hv⟩ := (contains_some_iff M _ _).1 h
    rcases ρ' with _ | ⟨j', kk'⟩
    · exact Relation.ReflTransGen.single (adj_outside M hw hv ((contains_none_iff M _).1 h'))
    · obtain ⟨hw', hv'⟩ := (contains_some_iff M _ _).1 h'
      exact sq_chain M hw hw' hv hv'


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
