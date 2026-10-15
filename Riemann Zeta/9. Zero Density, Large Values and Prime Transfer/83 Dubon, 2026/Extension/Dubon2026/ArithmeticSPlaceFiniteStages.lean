import Dubon2026.OriginalSPlaceClassBaseChange
import Dubon2026.ArithmeticSUnitFiniteTransitions

/-! # Source idele and class transitions at the actual arithmetic finite stages

The same exceptional integer supplies the exact pullback of supports, with
no support premise. Thus the original finite S-unit coefficient, source idele
coefficient and source class quotient have compatible actual stage maps.
This is the fixed-support system needed for Milne I.4 on the DUB-17 route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (hEF : E ≤ F)

local instance : NumberField E := NumberField.of_module_finite K E
local instance : NumberField F := NumberField.of_module_finite K F

/-- The original arithmetic exceptional support pulls back along the actual finite-stage inclusion. -/
theorem arithmeticSPlaceFiniteStage_support
    (w : HeightOneSpectrum (𝓞 F)) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    w ∈ arithmeticSUnitFiniteStageSupport K Ω a ha F ↔
      originalFinitePrimeBelow E F w ∈ arithmeticSUnitFiniteStageSupport K Ω a ha E := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  change w ∈ originalExceptionalIntegerSupport F _ _ ↔
    originalFinitePrimeBelow E F w ∈ originalExceptionalIntegerSupport E _ _
  rw [mem_originalExceptionalIntegerSupport, mem_originalExceptionalIntegerSupport]
  change algebraMap (𝓞 K) (𝓞 F) a ∈ w.asIdeal ↔
    algebraMap (𝓞 E) (𝓞 F) (algebraMap (𝓞 K) (𝓞 E) a) ∈ w.asIdeal
  rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 E) (𝓞 F)]

/-- The source S-place coefficient of the actual finite arithmetic field. -/
abbrev ArithmeticSPlaceFiniteStageRep :=
  supportedUnrestrictedUnitRep K E (arithmeticSUnitFiniteStageSupport K Ω a ha E)
    (originalExceptionalIntegerSupport_galoisStable E K a ha)

/-- The source S-place class coefficient of the same finite arithmetic field. -/
abbrev ArithmeticSPlaceClassFiniteStageRep :=
  originalSPlaceIdeleClassRep K E (arithmeticSUnitFiniteStageSupport K Ω a ha E)
    (originalExceptionalIntegerSupport_galoisStable E K a ha)

/-- The original diagonal from the same finite S-unit coefficient used in the proved H2 colimit. -/
def arithmeticSPlaceFiniteStagePrincipal :
    arithmeticSUnitFiniteStageRep K Ω a ha E ⟶ ArithmeticSPlaceFiniteStageRep K Ω a ha E :=
  originalSPlacePrincipalRepHom K E _ _

/-- The original source class quotient at the same actual finite arithmetic field. -/
def arithmeticSPlaceFiniteStageQuotient :
    ArithmeticSPlaceFiniteStageRep K Ω a ha E ⟶ ArithmeticSPlaceClassFiniteStageRep K Ω a ha E :=
  originalSPlaceIdeleClassRepHom K E _ _

/-- Actual arithmetic source idele transition, using the proved support pullback. -/
def arithmeticSPlaceFiniteTransition :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    restrictedCoefficientRep (ArithmeticSPlaceFiniteStageRep K Ω a ha E)
      (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)) ⟶
        ArithmeticSPlaceFiniteStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  exact originalSPlaceBaseChangeRepHom K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)

/-- Actual arithmetic source class transition, induced on the original quotient at the proved support. -/
def arithmeticSPlaceClassFiniteTransition :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    restrictedCoefficientRep (ArithmeticSPlaceClassFiniteStageRep K Ω a ha E)
      (AlgEquiv.restrictNormalHom E : Gal(F/K) →* Gal(E/K)) ⟶
        ArithmeticSPlaceClassFiniteStageRep K Ω a ha F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  exact originalSPlaceClassBaseChangeRepHom K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)

/-- The source idele stage transition commutes with the original S-unit transition already used by the arithmetic H2 colimit. -/
theorem arithmeticSPlaceFiniteTransition_principal
    (x : arithmeticSUnitFiniteStageRep K Ω a ha E) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    (arithmeticSPlaceFiniteTransition K Ω a ha E F hEF).hom
      ((arithmeticSPlaceFiniteStagePrincipal K Ω a ha E).hom x) =
        (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom
          ((arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF).hom x) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  have hu : (originalSUnitBaseChangeRepHom K E F _ _
      (originalExceptionalIntegerSupport_galoisStable E K a ha)
      (originalExceptionalIntegerSupport_galoisStable F K a ha)
      (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)).hom x =
        (arithmeticSUnitFiniteTransitionInclusion K Ω a ha E F hEF).hom x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact (arithmeticSUnitFiniteTransitionMap_coe K Ω a ha E F hEF x.toMul).symm
  exact (originalSPlaceBaseChangeRepHom_principal K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF) x).trans
      (congrArg (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom hu)

/-- The source class transition preserves the literal arithmetic finite-stage quotient map. -/
theorem arithmeticSPlaceClassFiniteTransition_quotient
    (x : ArithmeticSPlaceFiniteStageRep K Ω a ha E) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    (arithmeticSPlaceClassFiniteTransition K Ω a ha E F hEF).hom
      ((arithmeticSPlaceFiniteStageQuotient K Ω a ha E).hom x) =
        (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom
          ((arithmeticSPlaceFiniteTransition K Ω a ha E F hEF).hom x) := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  exact originalSPlaceClassBaseChangeRepHom_mk K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF) x

end
end Dubon2026
