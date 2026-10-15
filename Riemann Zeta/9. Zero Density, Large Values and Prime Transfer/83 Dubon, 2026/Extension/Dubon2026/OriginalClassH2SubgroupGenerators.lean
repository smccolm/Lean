import Dubon2026.OriginalH2GeneratorRestriction
import Dubon2026.OriginalCohomologyRestrictionTrace
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # Original arithmetic H2 subgroup generators

The genuine finite-Galois class theorem supplies every subgroup size bound,
and the original Shapiro comparison supplies literal restriction/corestriction.
Thus a single full-order class generates all subgroup H2 groups under actual
restriction. Constructing that class is the remaining input at this step of
DUB-17's normalized finite class invariants and reverse localization route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory groupCohomology

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Original subgroup class H2 is finite with order at most the actual subgroup order. -/
theorem originalIdeleClass_subgroup_second_finite_card_le (S : Subgroup Gal(L/K)) :
    Finite (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) ∧
      Nat.card (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) ≤
        Nat.card S := by
  let F := IntermediateField.fixedField S
  let e := (originalIdeleClassSubgroupCohomologyIso S 2).toLinearEquiv.toEquiv
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd F L
  haveI := hf
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e]
  have hle := Nat.le_of_dvd (Module.finrank_pos (R := F) (M := L)) hd
  exact hle.trans_eq (IntermediateField.finrank_fixedField_eq_card S)

/-- A full-order original class restricts to generators of every subgroup H2, with no assumed trace or subgroup-size premises. -/
theorem originalIdeleClass_full_order_restricts_to_generators
    (u : groupCohomology (originalIdeleClassRep K L) 2)
    (hu : addOrderOf u = Module.finrank K L) :
    (∀ S : Subgroup Gal(L/K),
      Nat.card (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) = Nat.card S) ∧
    (∀ S : Subgroup Gal(L/K), Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom u} = ⊤) := by
  classical
  letI (S : Subgroup Gal(L/K)) : Fintype (Gal(L/K) ⧸ S) := Fintype.ofFinite _
  have horder : addOrderOf u = Nat.card Gal(L/K) :=
    hu.trans (IsGalois.card_aut_eq_finrank K L).symm
  have hsize : ∀ (S : Subgroup Gal(L/K)) [Fintype S],
      Finite (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) ∧
        Nat.card (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) ≤ Fintype.card S := by
    intro S _
    simpa only [Nat.card_eq_fintype_card (α := S)] using
      originalIdeleClass_subgroup_second_finite_card_le K L S
  obtain ⟨hcard, hgen⟩ := originalH2_generator_restricts_to_subgroups
    (originalIdeleClassRep K L) u horder hsize
    (fun S => (subgroupCohomologyTrace (originalIdeleClassRep K L) S 2).hom)
    (fun S x => originalCohomology_trace_restriction_apply (originalIdeleClassRep K L) S 2 x)
  refine ⟨fun S => ?_, hgen⟩
  letI : Fintype S := Fintype.ofFinite S
  exact (hcard S).trans Nat.card_eq_fintype_card.symm

end
end Dubon2026
