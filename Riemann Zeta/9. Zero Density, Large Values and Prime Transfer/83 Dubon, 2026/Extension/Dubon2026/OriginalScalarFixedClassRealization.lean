import Dubon2026.OriginalScalarFixedFieldInUnion
import Dubon2026.OriginalDegreeOneBaseClassChange

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)

/-- Keep the original union's rational algebra. -/
local instance scalarClassRealizationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Keep each displayed finite stage's rational algebra. -/
local instance scalarClassRealizationFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Keep the actual algebra on each intermediate fixed field and image. -/
local instance scalarClassRealizationIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Full-class H2 over the literal realized fixed-field extension. -/
abbrev originalScalarFixedFieldRealizedClassH2
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a) (S : Subgroup Gal(L.val/ℚ)) :=
  let F := originalScalarFixedFieldInUnion Ω a L S
  let M := originalUnramifiedStageInUnion a L
  letI : Algebra F M := (IntermediateField.inclusion (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra
  letI : Module F M := (IntermediateField.inclusion (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra.toSMul
  groupCohomology (originalIdeleClassRep F M) 2

/-- Transport the actual fixed-field full class through the two original
field embeddings to its literal arithmetic-union realization. -/
def originalScalarFixedFieldClassRealization
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a) (S : Subgroup Gal(L.val/ℚ)) :
    groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L.val) 2 →ₗ[ℤ]
      originalScalarFixedFieldRealizedClassH2 Ω a L S := by
  let K := IntermediateField.fixedField S
  let F := originalScalarFixedFieldInUnion Ω a L S
  let M := originalUnramifiedStageInUnion a L
  let eK := originalScalarFixedFieldInUnionEquiv Ω a L S
  let eL := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra
  letI : Module F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra.toSMul
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S))
  letI : Algebra K F := eK.toAlgHom.toAlgebra
  letI : Module K F := eK.toAlgHom.toAlgebra.toModule
  letI : SMul K F := eK.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ K F := IsScalarTower.of_algHom eK.toAlgHom
  letI : Algebra L.val M := eL.toAlgHom.toAlgebra
  letI : Module L.val M := eL.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := eL.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom eL.toAlgHom
  letI : Algebra K M := (eL.toAlgHom.comp K.val).toAlgebra
  letI : Module K M := (eL.toAlgHom.comp K.val).toAlgebra.toModule
  letI : SMul K M := (eL.toAlgHom.comp K.val).toAlgebra.toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (eL.toAlgHom.comp K.val)
  letI : IsScalarTower K L.val M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  letI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  letI : IsGalois K M := IsGalois.tower_top_of_isGalois ℚ K M
  exact (groupCohomology.map (galoisBaseChangeRestriction K F L.val M)
    (originalFullClassFieldBaseChangeRepHom K F L.val M) 2).hom

/-- The literal realized class detects the original fixed-field class:
injectivity follows from finite class inflation and the degree-one base. -/
theorem originalScalarFixedFieldClassRealization_injective
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a) (S : Subgroup Gal(L.val/ℚ)) :
    Function.Injective (originalScalarFixedFieldClassRealization Ω a L S) := by
  let K := IntermediateField.fixedField S
  let F := originalScalarFixedFieldInUnion Ω a L S
  let M := originalUnramifiedStageInUnion a L
  let eK := originalScalarFixedFieldInUnionEquiv Ω a L S
  let eL := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra
  letI : Module F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S)).toAlgebra.toSMul
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L S))
  letI : Algebra K F := eK.toAlgHom.toAlgebra
  letI : Module K F := eK.toAlgHom.toAlgebra.toModule
  letI : SMul K F := eK.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ K F := IsScalarTower.of_algHom eK.toAlgHom
  letI : Algebra L.val M := eL.toAlgHom.toAlgebra
  letI : Module L.val M := eL.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := eL.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom eL.toAlgHom
  letI : Algebra K M := (eL.toAlgHom.comp K.val).toAlgebra
  letI : Module K M := (eL.toAlgHom.comp K.val).toAlgebra.toModule
  letI : SMul K M := (eL.toAlgHom.comp K.val).toAlgebra.toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (eL.toAlgHom.comp K.val)
  letI : IsScalarTower K L.val M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' (by ext x; rfl)
  letI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  letI : IsGalois K M := IsGalois.tower_top_of_isGalois ℚ K M
  have hKF : Module.finrank K F = 1 := Module.finrank_of_bijective_algebraMap eK.bijective
  exact originalFullClassFieldBaseChangeH2_injective_of_base_degree_one K F L.val M hKF

end
end Dubon2026
