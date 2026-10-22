import Dubon2026.SourceCellGridSquareSidePartner

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

theorem adj_right {j kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j + 1, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j + 1, kk)).K) : Adj M v (some (j, kk)) (some (j + 1, kk)) := by
  obtain ⟨⟨hj, -⟩, -⟩ := (mem_win_iff M).1 hw
  obtain ⟨⟨-, r2⟩, i1, i2⟩ := of_mem_baseK M hv
  obtain ⟨⟨r1', -⟩, -⟩ := of_mem_baseK M hv'
  have hre : v.re = M.o + (j + 1) * M.hm := le_antisymm r2 (by exact_mod_cast r1')
  have D := arcData_base M j kk
  by_cases hc : (M.ctr (j, kk)).im ≤ v.im
  · obtain ⟨a0, ha0⟩ := exists_idx M (j, kk) 0 (by omega)
    obtain ⟨a2, ha2⟩ := exists_idx M (j + 1, kk) 2 (by omega)
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a0, D.arc0 a0 ha0⟩)
      ((shares_some_iff M _ _).2 ⟨hw', a2, (right_arc₀₂ M hj rfl a0 ha0 a2 ha2).symm.trans (D.arc0 a0 ha0)⟩)
      (mem_vseg.2 ⟨hre, hc, i2⟩)
  · obtain ⟨a5, ha5⟩ := exists_idx M (j, kk) 5 (by omega)
    obtain ⟨a3, ha3⟩ := exists_idx M (j + 1, kk) 3 (by omega)
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a5, D.arc5 a5 ha5⟩)
      ((shares_some_iff M _ _).2 ⟨hw', a3, (right_arc₅₃ M hj rfl a5 ha5 a3 ha3).symm.trans (D.arc5 a5 ha5)⟩)
      (mem_vseg.2 ⟨hre, i1, (not_le.mp hc).le⟩)

theorem adj_upper {j kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j, kk + 1) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j, kk + 1)).K) : Adj M v (some (j, kk)) (some (j, kk + 1)) := by
  obtain ⟨⟨r1, r2⟩, -, i2⟩ := of_mem_baseK M hv
  obtain ⟨-, i1', -⟩ := of_mem_baseK M hv'
  have him : v.im = M.o + (kk + 1) * M.hm := le_antisymm i2 (by exact_mod_cast i1')
  have D := arcData_base M j kk
  obtain ⟨a1, ha1⟩ := exists_idx M (j, kk) 1 (by omega)
  obtain ⟨a4, ha4⟩ := exists_idx M (j, kk + 1) 4 (by omega)
  exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a1, D.arc1 a1 ha1⟩)
    ((shares_some_iff M _ _).2 ⟨hw', a4, (upper_arc₁₄ M rfl a1 ha1 a4 ha4).symm.trans (D.arc1 a1 ha1)⟩)
    (mem_hseg.2 ⟨him, r1, r2⟩)


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
