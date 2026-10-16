import Dubon2026.OriginalClassesModOutsideH2Comparison
import Dubon2026.OriginalClassQuotientSubgroupCohomology
import Dubon2026.OriginalClassH2SubgroupGenerators

/-! # Subgroup generators for the original outside-unit class quotient

Reuse the proved full-class comparison over actual fixed fields and the
existing restriction/trace generator argument. This supplies the finite
quotient coefficient required by DUB-17's class/Ext duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (hu : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
    w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal)

include hu

/-- Every actual subgroup quotient H2 is finite with order bounded by the subgroup order. -/
theorem originalClassQuotient_subgroup_second_finite_card_le (H : Subgroup Gal(L/K)) :
    Finite (groupCohomology (Rep.res H.subtype
      (originalIdeleClassesModOutsideRep K L S hS)) 2) ∧
    Nat.card (groupCohomology (Rep.res H.subtype
      (originalIdeleClassesModOutsideRep K L S hS)) 2) ≤ Nat.card H := by
  let F := IntermediateField.fixedField H
  let e := (originalClassesModOutsideH2Iso F L S
    (originalClassQuotient_fixedField_support K L S hS H) hu ≪≫
      originalClassQuotientSubgroupCohomologyIso K L S hS H 2).toLinearEquiv.toEquiv
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd F L
  haveI := hf
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e]
  exact (Nat.le_of_dvd (Module.finrank_pos (R := F) (M := L)) hd).trans_eq
    (IntermediateField.finrank_fixedField_eq_card H)

/-- A full-order original quotient class generates H2 of every subgroup under literal restriction. -/
theorem originalClassQuotient_full_order_restricts_to_generators
    (u : groupCohomology (originalIdeleClassesModOutsideRep K L S hS) 2)
    (ho : addOrderOf u = Module.finrank K L) :
    (∀ H : Subgroup Gal(L/K),
      Nat.card (groupCohomology (Rep.res H.subtype
        (originalIdeleClassesModOutsideRep K L S hS)) 2) = Nat.card H) ∧
    (∀ H : Subgroup Gal(L/K), Submodule.span ℤ
      {(groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype
        (originalIdeleClassesModOutsideRep K L S hS))) 2).hom u} = ⊤) := by
  classical
  let A := originalIdeleClassesModOutsideRep K L S hS
  letI (H : Subgroup Gal(L/K)) : Fintype (Gal(L/K) ⧸ H) := Fintype.ofFinite _
  have horder : addOrderOf u = Nat.card Gal(L/K) :=
    ho.trans (IsGalois.card_aut_eq_finrank K L).symm
  have hsize : ∀ (H : Subgroup Gal(L/K)) [Fintype H],
      Finite (groupCohomology (Rep.res H.subtype A) 2) ∧
        Nat.card (groupCohomology (Rep.res H.subtype A) 2) ≤ Fintype.card H := by
    intro H _
    simpa only [Nat.card_eq_fintype_card (α := H)] using
      originalClassQuotient_subgroup_second_finite_card_le K L S hS hu H
  obtain ⟨hcard, hgen⟩ := originalH2_generator_restricts_to_subgroups A u horder hsize
    (fun H => (subgroupCohomologyTrace A H 2).hom)
    (fun H x => originalCohomology_trace_restriction_apply A H 2 x)
  refine ⟨fun H => ?_, hgen⟩
  letI : Fintype H := Fintype.ofFinite H
  exact (hcard H).trans Nat.card_eq_fintype_card.symm

end
end Dubon2026
