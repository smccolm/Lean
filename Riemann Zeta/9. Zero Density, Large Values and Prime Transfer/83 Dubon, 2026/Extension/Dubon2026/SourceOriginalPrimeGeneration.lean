import Dubon2026.SourceOriginalFieldGeneration
import Mathlib.FieldTheory.Relrank

/-! DUB-17/18 -> numerical modular genus -> original j-map degree.
At prime level the literal divisor-generated field has exactly j and
j(q^p) as generators, also after the original coefficient extension.
This identifies the proved prime simple extension with the actual full
field used by the canonical divisor and regular differential theorems.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem divisorExpansions_prime (p : ℕ) [hp : Fact p.Prime] :
    divisorExpansions p = ({jq, qExpand ℚ p jq} : Set (LaurentSeries ℚ)) := by
  ext x
  constructor
  · rintro ⟨d, _, hd, rfl⟩
    rcases (Nat.dvd_prime hp.out).mp hd with rfl | rfl
    · rw [qExpand_one_apply]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact ⟨1, inferInstance, one_dvd p, (qExpand_one_apply jq).symm⟩
    · rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨p, inferInstance, dvd_rfl, rfl⟩

theorem original_prime_field_eq_adjoin_pair (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] :
    modularFunctionFieldOver p L = IntermediateField.adjoin L
      ({coeffEmb L jq, coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L)) := by
  rw [modularFunctionFieldOver, laurentBaseChange_full_eq_adjoin,
    divisorExpansions_prime, Set.image_insert_eq, Set.image_singleton]

theorem original_prime_field_eq_simple_restrict (p : ℕ) [Fact p.Prime]
    (L : Type*) [Field L] [Algebra ℚ L] :
    modularFunctionFieldOver p L =
      (IntermediateField.adjoin (IntermediateField.adjoin L
        ({coeffEmb L jq} : Set (LaurentSeries L)))
        ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))).restrictScalars L := by
  rw [original_prime_field_eq_adjoin_pair]
  simpa only [Set.singleton_union] using
    (adjoin_adjoin_left L ({coeffEmb L jq} : Set (LaurentSeries L))
      ({coeffEmb L (qExpand ℚ p jq)} : Set (LaurentSeries L))).symm

end
end Dubon2026.SourceFunctionField
