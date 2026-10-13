import Dubon2026.OriginalIdeleClassNormalInvariants
import Dubon2026.SecondCohomologyNormalSubgroupCardinality

/-! # Original idele-class cohomology through actual fixed fields

The pinned H1 exact sequence and proved H2 cardinal divisibility apply
after the literal fixed-field coefficient comparisons. These deductions
are used by finite p-group induction for DUB-17's class-field and global
invariant dependency; their smaller-field hypotheses are discharged there.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Vanishing over the two actual fixed-field extensions forces original H1 to vanish. -/
theorem originalIdeleClass_first_zero_of_fixedField
    (hQ : Limits.IsZero (groupCohomology
      (originalIdeleClassRep K (IntermediateField.fixedField S)) 1))
    (hS : Limits.IsZero (groupCohomology
      (originalIdeleClassRep (IntermediateField.fixedField S) L) 1)) :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) := by
  let A := originalIdeleClassRep K L
  have hQ' := hQ.of_iso (originalIdeleClassNormalInvariantCohomologyIso S 1).symm
  have hS' := hS.of_iso (originalIdeleClassSubgroupCohomologyIso S 1).symm
  exact (groupCohomology.H1InfRes_exact A S).isZero_X₂
    (hQ'.eq_zero_of_src _) (hS'.eq_zero_of_tgt _)

/-- Actual original H2 is finite with order dividing the product of the two fixed-field H2 orders. -/
theorem originalIdeleClass_second_fixedField_card_dvd
    (hfirst : Limits.IsZero (groupCohomology
      (originalIdeleClassRep (IntermediateField.fixedField S) L) 1))
    [Finite (groupCohomology (originalIdeleClassRep K (IntermediateField.fixedField S)) 2)]
    [Finite (groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L) 2)] :
    Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) ∣
        Nat.card (groupCohomology (originalIdeleClassRep K (IntermediateField.fixedField S)) 2) *
          Nat.card (groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L) 2) := by
  let eQ := originalIdeleClassNormalInvariantCohomologyIso S 2
  let eS := originalIdeleClassSubgroupCohomologyIso S 2
  haveI : Finite (groupCohomology ((originalIdeleClassRep K L).quotientToInvariants S) 2) :=
    Finite.of_equiv _ eQ.toLinearEquiv.toEquiv
  haveI : Finite (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) :=
    Finite.of_equiv _ eS.toLinearEquiv.toEquiv
  obtain ⟨hf, hd⟩ := secondCohomology_normal_subgroup_card_dvd (originalIdeleClassRep K L) S
    (hfirst.of_iso (originalIdeleClassSubgroupCohomologyIso S 1).symm)
  refine ⟨hf, ?_⟩
  have hQ := Nat.card_congr eQ.toLinearEquiv.toEquiv
  have hS := Nat.card_congr eS.toLinearEquiv.toEquiv
  rwa [← hQ, ← hS] at hd

end
end Dubon2026
