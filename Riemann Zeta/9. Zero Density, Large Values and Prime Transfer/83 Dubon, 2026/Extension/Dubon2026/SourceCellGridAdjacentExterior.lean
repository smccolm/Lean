import Dubon2026.SourceCellGridAdjacentSquares

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

theorem adj_outside {j kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hv : v ∈ (M.base (j, kk)).K) (hout : v ∉ M.winReg.Kint) : Adj M v (some (j, kk)) none := by
  obtain ⟨⟨hj, hj2⟩, hk, hk2⟩ := (mem_win_iff M).1 hw
  obtain ⟨⟨r1, r2⟩, i1, i2⟩ := of_mem_baseK M hv
  rcases not_mem_winKint M hout with h1 | h2 | h3 | h4
  ·
    have hjj : j = M.jlo := le_antisymm (int_le_of_grid₀₀ M.hhm (r1.trans h1)) hj
    subst hjj
    have hre : v.re = M.o + M.jlo * M.hm := le_antisymm h1 r1
    by_cases hc : M.cy (M.jlo, kk) ≤ v.im
    · obtain ⟨a2, ha2⟩ := exists_idx M (M.jlo, kk) 2 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_leftUpper M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2 ⟨hw, a2, SideIdentity.arcSet_eq_leftUpper (isSquare_base M M.jlo kk) (yL_jlo M kk) a2 ha2⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, hc, i2⟩
    · obtain ⟨a3, ha3⟩ := exists_idx M (M.jlo, kk) 3 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_leftLower M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2 ⟨hw, a3, SideIdentity.arcSet_eq_leftLower (isSquare_base M M.jlo kk) (yL_jlo M kk) a3 ha3⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, i1, (not_le.mp hc).le⟩
  ·
    have hjj : j = M.jhi := le_antisymm hj2 (int_le_of_grid₁₁ M.hhm (h2.trans r2))
    subst hjj
    have hre : v.re = M.o + (M.jhi + 1) * M.hm := le_antisymm r2 h2
    by_cases hc : M.cy (M.jhi, kk) ≤ v.im
    · obtain ⟨a0, ha0⟩ := exists_idx M (M.jhi, kk) 0 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_rightUpper M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2
          ⟨hw, a0, SideIdentity.arcSet_eq_rightUpper (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a0 ha0⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, hc, i2⟩
    · obtain ⟨a5, ha5⟩ := exists_idx M (M.jhi, kk) 5 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_rightLower M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2
          ⟨hw, a5, SideIdentity.arcSet_eq_rightLower (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a5 ha5⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, i1, (not_le.mp hc).le⟩
  ·
    have hkk : kk = M.klo := le_antisymm (int_le_of_grid₀₀ M.hhm (i1.trans h3)) hk
    subst hkk
    have him : v.im = M.o + M.klo * M.hm := le_antisymm h3 i1
    obtain ⟨a4, ha4⟩ := exists_idx M (j, M.klo) 4 (by omega)
    obtain ⟨k₀, hk₀⟩ := win_bottom M j hj hj2
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a4, SideIdentity.arcSet_eq_bottom (isSquare_base M j M.klo) a4 ha4⟩)
      ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨him, r1, r2⟩
  ·
    have hkk : kk = M.khi := le_antisymm hk2 (int_le_of_grid₁₁ M.hhm (h4.trans i2))
    subst hkk
    have him : v.im = M.o + (M.khi + 1) * M.hm := le_antisymm i2 h4
    obtain ⟨a1, ha1⟩ := exists_idx M (j, M.khi) 1 (by omega)
    obtain ⟨k₀, hk₀⟩ := win_top M j hj hj2
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a1, SideIdentity.arcSet_eq_top (isSquare_base M j M.khi) a1 ha1⟩)
      ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨him, r1, r2⟩


end
end Dubon2026.SourceFunctionField.CellGeometry.StarProperty
