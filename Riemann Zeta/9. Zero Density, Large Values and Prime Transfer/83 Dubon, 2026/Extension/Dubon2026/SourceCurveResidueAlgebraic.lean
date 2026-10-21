import Dubon2026.SourceCurvePlaceRestriction
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! DUB-17/18 -> regular differential dimension/local regularity -> finite
residue fields over algebraically closed constants. A transcendental residue
class would put its entire lifted rational function field in the valuation
ring. Finiteness over that coordinate then contradicts properness of the
integrally closed valuation ring. This avoids rational-place classification.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open Polynomial IsLocalRing

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adjoin_mem_of_transcendental_residue (a : v.toValuationSubring)
    (ht : Transcendental K (residue v.toValuationSubring a))
    (z : IntermediateField.adjoin K ({(a : F)} : Set F)) :
    (z : F) ∈ v.toValuationSubring := by
  let φ := IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField
  let ψ := IsScalarTower.toAlgHom K v.toValuationSubring F
  have hcoe (p : K[X]) : ((aeval a p : v.toValuationSubring) : F) = aeval (a : F) p :=
    (aeval_algHom_apply ψ a p).symm
  obtain ⟨p, q, he⟩ := (IntermediateField.mem_adjoin_simple_iff K (z : F)).mp z.2
  rw [he, div_eq_mul_inv]
  refine mul_mem (hcoe p ▸ (aeval a p : v.toValuationSubring).2) ?_
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hres : residue v.toValuationSubring (aeval a q) ≠ 0 := by
    change φ (aeval a q) ≠ 0
    rw [← aeval_algHom_apply]
    exact fun h => hq ((transcendental_iff_injective.mp ht) (by simpa using h))
  have hu := (residue_ne_zero_iff_isUnit (aeval a q)).mp hres
  have ho := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec, hcoe] at ho
  apply v.mem_of_ord_nonneg
  rw [v.ord_inv, ho, neg_zero]

theorem isAlgebraic_residue_of_finite_coordinates
    (hfinite : ∀ t : F, Transcendental K t →
      FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F)
    (y : v.ResidueField) : IsAlgebraic K y := by
  classical
  by_contra ht
  obtain ⟨a, rfl⟩ := residue_surjective (R := v.toValuationSubring) y
  have htr : Transcendental K (a : F) := by
    intro ha
    have hi : IsIntegral K a :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom K v.toValuationSubring F)
        Subtype.val_injective).mp ha.isIntegral
    exact ht ((hi.map (IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField)).isAlgebraic)
  let E := IntermediateField.adjoin K ({(a : F)} : Set F)
  haveI : FiniteDimensional E F := hfinite (a : F) htr
  apply v.comap_algebraMap_ne_top (F := E)
  apply top_le_iff.mp
  intro z _
  exact v.adjoin_mem_of_transcendental_residue a ht z

end
end Dubon2026.SourceCurve.Place
