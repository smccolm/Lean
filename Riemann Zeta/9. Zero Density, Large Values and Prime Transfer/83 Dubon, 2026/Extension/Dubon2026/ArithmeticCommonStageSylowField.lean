import Dubon2026.OriginalScalarSylowRealizationDegree
import Dubon2026.ArithmeticRelativeStageIdeleCohomology

/-! The actual common-field Sylow fixed field for DUB-17's source-cup
comparison. Its literal lift stays inside the same arithmetic union;
Mathlib's fixed-field degree theorem supplies its prime-power degree. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat

/-- Keep the actual rational inclusion on intermediate fields. -/
local instance commonSylowIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Keep the actual rational inclusion on finite Galois stages. -/
local instance commonSylowFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable (a : 𝓞 ℚ)
  (M : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The actual subgroup fixed field, lifted through the common stage's inclusion. -/
def arithmeticCommonStageFixedField (S : Subgroup Gal(M/ℚ)) :
    IntermediateField ℚ (rationalUnramifiedExtension a) :=
  IntermediateField.lift (F := M.toIntermediateField) (IntermediateField.fixedField S)

/-- The lifted fixed field lies in the same common finite field. -/
theorem arithmeticCommonStageFixedField_le (S : Subgroup Gal(M/ℚ)) :
    arithmeticCommonStageFixedField a M S ≤ M.toIntermediateField :=
  IntermediateField.lift_le _

/-- The literal lifted Sylow fixed field has prime-power relative degree;
the common upper field is preserved and no degree premise is supplied. -/
theorem arithmeticCommonStageSylowFixedField_degree
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(M/ℚ)) :
    let E := arithmeticCommonStageFixedField a M (S : Subgroup Gal(M/ℚ))
    letI : Algebra E M := (IntermediateField.inclusion
      (arithmeticCommonStageFixedField_le a M (S : Subgroup Gal(M/ℚ)))).toAlgebra
    letI : Module E M := Algebra.toModule
    ∃ t : ℕ, Module.finrank E M = p ^ t := by
  let K := IntermediateField.fixedField (S : Subgroup Gal(M/ℚ))
  let E := arithmeticCommonStageFixedField a M (S : Subgroup Gal(M/ℚ))
  let e : K ≃ₐ[ℚ] E := IntermediateField.liftAlgEquiv K
  letI : Algebra E M := (IntermediateField.inclusion
    (arithmeticCommonStageFixedField_le a M (S : Subgroup Gal(M/ℚ)))).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := Algebra.toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion
    (arithmeticCommonStageFixedField_le a M (S : Subgroup Gal(M/ℚ))))
  letI : Algebra K E := e.toAlgHom.toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := Algebra.toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom e.toAlgHom
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Free K E := Module.Free.of_divisionRing K E
  letI : Module.Free E M := Module.Free.of_divisionRing E M
  have hKE : Module.finrank K E = 1 := Module.finrank_of_bijective_algebraMap e.bijective
  have hdegree : Module.finrank E M = Module.finrank K M := by
    simpa only [hKE, one_mul] using Module.finrank_mul_finrank K E M
  obtain ⟨t, ht⟩ := S.isPGroup'.exists_card_eq
  exact ⟨t, hdegree.trans ((IntermediateField.finrank_fixedField_eq_card
    (S : Subgroup Gal(M/ℚ))).trans ht)⟩

end
end Dubon2026
