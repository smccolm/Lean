import Dubon2026.SourceRadialMeromorphicLocalAtlasData
import Dubon2026.SourceRadialMeromorphicCellDifferences

/-! DUB-17/18 -> cover Abel converse -> pole-avoiding path atlas.
Changes of local logarithm are integral residue periods. Actual carrier
intersection chains then place overlaps of the corrected atlas in the sum
of paired jumps and residue periods. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set Filter Complex RadialDissectionPeriods
open MeromorphicPeriods (Lg_sub_Lg)
open scoped Real Topology
variable {X R : Type*} [TopologicalSpace X]

theorem Gθ_sub_mem {D : RadialCellDissection X} (S : Finset X)
    (residue : X → R → ℂ) (hS : PolePos D S)
    {Ψ : R → D.ιC → ℂ → ℂ} {J : D.ιE → R → ℂ}
    (hJ : IsJumpH D (hfun S residue Ψ) J) {x x' y : X}
    (hy : y ∈ Uset D S x) (hy' : y ∈ Uset D S x') :
    Gθ S residue Ψ x y - Gθ S residue Ψ x' y ∈ ΛJ D S residue J := by
  obtain ⟨hxS, hyb, hyS⟩ := mem_Uset hy
  obtain ⟨hxS', hyb', -⟩ := mem_Uset hy'
  set C := cellOf D y with hCdef
  have hxD : x ∈ (D.cell C).carrier := mem_carrier_of_not_mem_badCarrierSet D hyb (mem_cellOf D y)
  have hxD' : x' ∈ (D.cell C).carrier := mem_carrier_of_not_mem_badCarrierSet D hyb' (mem_cellOf D y)

  have hlog : Φloc S residue Ψ C x y - Φloc S residue Ψ C x' y ∈ ΛJ D S residue J := by
    by_cases hρ : ρ D S residue C = 0
    · have : Φloc S residue Ψ C x y - Φloc S residue Ψ C x' y = 0 := by
        funext r
        simp only [Φloc, Pi.sub_apply, Pi.zero_apply, hρ]
        ring
      rw [this]; exact zero_mem _
    · have hc := ζ_ne_q S residue hS hxS hxD hρ
      have hc' := ζ_ne_q S residue hS hxS' hxD' hρ
      have hw := ζ_ne_q S residue hS hyS (mem_cellOf D y) hρ
      obtain ⟨n, hn⟩ := Lg_sub_Lg (q := (D.cell C).R.q) hc hc' hw
      have : Φloc S residue Ψ C x y - Φloc S residue Ψ C x' y =
          fun r => ρ D S residue C r * (n * (2 * π * I)) := by
        funext r
        simp only [Φloc, Pi.sub_apply]
        rw [← hn]
        ring
      rw [this]
      exact AddSubgroup.mem_sup_right (zsmul_ρ_mem_Λres S residue C n)
  have h1 := pval_sub_mem S residue hJ hxD (mem_cellOf D x)
  have h2 := pval_sub_mem S residue hJ hxD' (mem_cellOf D x')
  have : Gθ S residue Ψ x y - Gθ S residue Ψ x' y =
      (Φloc S residue Ψ C x y - Φloc S residue Ψ C x' y) -
        (pval S residue Ψ C x - pval S residue Ψ (cellOf D x) x) +
        (pval S residue Ψ C x' - pval S residue Ψ (cellOf D x') x') := by
    simp only [Gθ, hCdef]; abel
  rw [this]
  exact add_mem (sub_mem hlog h1) h2

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
