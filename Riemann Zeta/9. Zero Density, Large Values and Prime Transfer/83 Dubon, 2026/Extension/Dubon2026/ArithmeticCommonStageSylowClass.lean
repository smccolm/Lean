import Dubon2026.ArithmeticCommonStageSylowField
import Dubon2026.OriginalIdeleClassSylowDetection
import Dubon2026.OriginalClassTowerRestrictionComposition

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat

/-- Keep the actual rational inclusion on intermediate fields. -/
local instance commonSylowClassIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Keep the actual rational inclusion on finite Galois stages. -/
local instance commonSylowClassFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable (a : 𝓞 ℚ)
  (M : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The common finite arithmetic field is a number field. -/
local instance commonSylowClassNumberField : NumberField M := NumberField.of_module_finite ℚ M

/-- A prime-annihilated full class at the actual common field vanishes
exactly when its restriction to the lifted Sylow fixed field vanishes.
The image-field change has degree one and is proved injective on H2. -/
theorem arithmeticCommonStageClass_eq_zero_iff_sylow
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(M/ℚ))
    (x : groupCohomology (originalIdeleClassRep ℚ M) 2) (hx : p • x = 0) :
    let E := arithmeticCommonStageFixedField a M (S : Subgroup Gal(M/ℚ))
    letI : Algebra E M := (IntermediateField.inclusion
      (arithmeticCommonStageFixedField_le a M (S : Subgroup Gal(M/ℚ)))).toAlgebra
    letI : Module E M := Algebra.toModule
    letI : SMul E M := Algebra.toSMul
    letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion
      (arithmeticCommonStageFixedField_le a M (S : Subgroup Gal(M/ℚ))))
    x = 0 ↔ originalIdeleClassTowerH2Restriction ℚ E M x = 0 := by
  have hdetect := originalIdeleClassH2_eq_zero_iff_sylow_fixedField ℚ M p S x hx
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
  have hKE : Module.finrank K E = 1 := Module.finrank_of_bijective_algebraMap e.bijective
  exact hdetect.trans
    (originalIdeleClassTowerH2Restriction_zero_iff_degree_one ℚ K E M hKE x)

end
end Dubon2026
