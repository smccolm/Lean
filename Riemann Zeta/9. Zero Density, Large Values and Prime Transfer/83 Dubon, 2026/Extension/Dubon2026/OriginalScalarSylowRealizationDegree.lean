import Dubon2026.OriginalScalarFixedFieldInUnion
import Dubon2026.OriginalScalarStageSylowDegree
import Dubon2026.OriginalDegreeOneSquareRank

/-! # Preserve the actual Sylow degree in the arithmetic-union realization

The two original range equivalences have relative degree one. Their
literal commuting square preserves the prime-power degree, providing
the exact finite-field input to the existing normalized class theorem.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ)

/-- Keep the original union's rational algebra. -/
local instance scalarSylowRealizationUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Keep each displayed finite stage's rational algebra. -/
local instance scalarSylowRealizationFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Keep the actual algebra on each intermediate fixed field and image. -/
local instance scalarSylowRealizationIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- The literal union realization of the same Sylow fixed-field extension
has the required prime-power degree, without a degree hypothesis. -/
theorem originalScalarSylowRealization_exists_prime_power_degree
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (S : Sylow p Gal(L.val/ℚ)) :
    let F := originalScalarFixedFieldInUnion Ω a L (S : Subgroup Gal(L.val/ℚ))
    let M := originalUnramifiedStageInUnion a L
    letI : Algebra F M := (IntermediateField.inclusion
      (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ)))).toAlgebra
    letI : Module F M := (IntermediateField.inclusion
      (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ)))).toAlgebra.toModule
    letI : SMul F M := (IntermediateField.inclusion
      (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ)))).toAlgebra.toSMul
    ∃ t : ℕ, Module.finrank F M = p ^ t := by
  let K := IntermediateField.fixedField (S : Subgroup Gal(L.val/ℚ))
  let F := originalScalarFixedFieldInUnion Ω a L (S : Subgroup Gal(L.val/ℚ))
  let M := originalUnramifiedStageInUnion a L
  let eK := originalScalarFixedFieldInUnionEquiv Ω a L (S : Subgroup Gal(L.val/ℚ))
  let eL := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ)))).toAlgebra
  letI : Module F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ)))).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ)))).toAlgebra.toSMul
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom (IntermediateField.inclusion
    (originalScalarFixedFieldInUnion_le Ω a L (S : Subgroup Gal(L.val/ℚ))))
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
  have hKF : Module.finrank K F = 1 := Module.finrank_of_bijective_algebraMap eK.bijective
  have hLM : Module.finrank L.val M = 1 := Module.finrank_of_bijective_algebraMap eL.bijective
  obtain ⟨t, ht⟩ := originalScalarStage_sylow_fixedField_degree Ω a L p S
  exact ⟨t, (originalDegreeOneSquare_finrank K F L.val M hKF hLM).trans ht⟩

end
end Dubon2026
