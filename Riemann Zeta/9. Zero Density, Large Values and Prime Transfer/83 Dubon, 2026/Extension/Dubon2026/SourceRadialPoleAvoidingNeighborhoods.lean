import Dubon2026.SourceRadialMeromorphicPrimitiveValues
import Dubon2026.SourceRadialCellCarrierNeighborhoods

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
Reuse the finite closed-carrier atlas and remove the marked pole set. The
source's extra ball restrictions are unnecessary: logarithm changes on overlaps
are integral periods wherever the displacement is nonzero, while derivative
comparison only needs a neighborhood of its center. Every used implication is
proved below, with no change to pole avoidance or the eventual path conclusion.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
noncomputable section
open Set RadialDissectionPeriods
variable {X R : Type*} [TopologicalSpace X]

/-- A finite carrier neighborhood excluding the marked poles. -/
def Uset (D : RadialCellDissection X) (S : Finset (X)) (x : X) : Set (X) := by
  classical
  exact if x ∈ S then ∅ else (badCarrierSet D x)ᶜ ∩ (S : Set (X))ᶜ

theorem isOpen_Uset [T2Space X] (D : RadialCellDissection X) (S : Finset (X)) (x : X) :
    IsOpen (Uset D S x) := by
  classical
  unfold Uset
  split_ifs
  · exact isOpen_empty
  · exact (isClosed_badCarrierSet D x).isOpen_compl.inter S.finite_toSet.isClosed.isOpen_compl

theorem mem_Uset_self (D : RadialCellDissection X) (S : Finset (X))
    {x : X} (hxS : x ∉ S) : x ∈ Uset D S x := by
  classical
  unfold Uset
  rw [if_neg hxS]
  exact ⟨not_mem_badCarrierSet_self D x, hxS⟩

theorem mem_Uset {D : RadialCellDissection X} {S : Finset (X)} {x y : X}
    (hy : y ∈ Uset D S x) : x ∉ S ∧ y ∉ badCarrierSet D x ∧ y ∉ S := by
  classical
  unfold Uset at hy
  split_ifs at hy with hxS
  · exact False.elim (notMem_empty y hy)
  · exact ⟨hxS, hy.1, hy.2⟩

theorem ζ_ne_q {D : RadialCellDissection X} (S : Finset (X)) (residue : X → R → ℂ)
    (hS : PolePos D S) {x : X} (hxS : x ∉ S) {C : D.ιC}
    (hxC : x ∈ (D.cell C).carrier) (hρ : ρ D S residue C ≠ 0) :
    (D.cell C).ζ x ≠ (D.cell C).R.q := by
  have hpole : ∃ v ∈ S, v ∈ (D.cell C).interior' := by
    by_contra h
    exact hρ (ρ_eq_zero residue (fun v hv hvC => h ⟨v, hv, hvC⟩))
  obtain ⟨v, hv, hvC⟩ := hpole
  have hq := (hS.center hv (RadialCell.interior_subset_carrier _ hvC)).2
  intro hx
  have hsrc : ∀ {y}, y ∈ (D.cell C).carrier → y ∈ (D.cell C).ζ.source := by
    rintro y ⟨z, hz, rfl⟩
    exact (D.cell C).ζ.map_target ((D.cell C).hKt hz)
  have he := (D.cell C).ζ.injOn (hsrc hxC) (hsrc (RadialCell.interior_subset_carrier _ hvC))
    (hx.trans hq.symm)
  exact hxS (he ▸ hv)

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialMeromorphicPeriods
