import Dubon2026.ArithmeticOriginalEnlargedClassColimitTransition
import Dubon2026.ArithmeticOriginalRelationClassTransport

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union inclusion. -/
local instance originalEnlargedRelationValuesUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual finite-stage rational inclusions. -/
local instance originalEnlargedRelationValuesFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[ℚ] F.val)
  (hi : ∀ x : P, (i x : Ω) = (x.val : Ω))

variable (B : Rep.{0} ℤ Gal(P/ℚ))

include hi in
/-- The relation transported to the exact enlarged scalar stage retains
the descended relation's original colimit value after the two canonical
relation-kernel maps. No coefficient-square premise is assumed. -/
theorem arithmeticOriginalEnlargedRelationClassTransport_colimit
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFL : F.val.toIntermediateField ≤ L.val.toIntermediateField)
    (φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha P) :
    letI : Algebra P F.val := i.toAlgebra
    letI : Module P F.val := i.toAlgebra.toModule
    letI : SMul P F.val := i.toAlgebra.toSMul
    letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
    letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
    letI : Module F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toModule
    letI : SMul F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toSMul
    letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
    let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
    let τ : Gal(F.val/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
    let υ : Gal(L.val/ℚ) →* Gal(F.val/ℚ) := AlgEquiv.restrictNormalHom F.val
    let BL := Rep.res υ BF
    ∀ z : originalRelationModule BL,
      (arithmeticOriginalStageClassToColimit Ω a ha L).hom
        ((arithmeticOriginalEnlargedRelationClassTransport Ω a ha P F i B L hFL φ).hom z) =
      (coefficientRepresentationColimitOf _
        (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) P).hom
        (φ.hom ((originalRelationGroupChange τ B).hom
          ((originalRelationGroupChange υ BF).hom z))) := by
  letI : Algebra P F.val := i.toAlgebra
  letI : Module P F.val := i.toAlgebra.toModule
  letI : SMul P F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
  letI : Algebra F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra
  letI : Module F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toModule
  letI : SMul F.val L.val := (IntermediateField.inclusion hFL).toRingHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ F.val L.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFL)
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
  let τ : Gal(F.val/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  let υ : Gal(L.val/ℚ) →* Gal(F.val/ℚ) := AlgEquiv.restrictNormalHom F.val
  let BL := Rep.res υ BF
  change ∀ z : originalRelationModule BL,
      (arithmeticOriginalStageClassToColimit Ω a ha L).hom
        ((arithmeticOriginalEnlargedRelationClassTransport Ω a ha P F i B L hFL φ).hom z) =
      (coefficientRepresentationColimitOf _
        (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) P).hom
        (φ.hom ((originalRelationGroupChange τ B).hom
          ((originalRelationGroupChange υ BF).hom z)))
  intro z
  exact arithmeticOriginalEnlargedClassToColimit_transition Ω a ha P F i hi L hFL
    (φ.hom ((originalRelationGroupChange τ B).hom
      ((originalRelationGroupChange υ BF).hom z)))

end
end Dubon2026
