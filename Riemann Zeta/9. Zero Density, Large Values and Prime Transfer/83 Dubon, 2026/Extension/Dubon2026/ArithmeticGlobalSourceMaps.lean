import Dubon2026.ArithmeticGlobalSourceColimits
import Dubon2026.ArithmeticSPlaceCoefficientColimits
import Dubon2026.CoefficientRepresentationColimitMap

/-! # Original equivariant source maps on the arithmetic coefficient colimits

The actual diagonal and quotient maps commute with global Galois actions and
the original stage transitions. Their induced colimit maps retain the exact
coefficient maps whose kernel and image were proved equal. This supplies the
equivariant source sequence needed by DUB-17's arithmetic duality route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- The literal finite-stage diagonal with its original global Galois action. -/
def arithmeticGlobalSPlaceStagePrincipal
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    arithmeticGlobalSUnitStageRep K Ω a ha F ⟶ arithmeticGlobalSPlaceStageRep K Ω a ha F :=
  Rep.ofHom {
    toLinearMap := (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom.toLinearMap
    isIntertwining' := fun g => LinearMap.ext (fun x =>
      Rep.hom_comm_apply (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F)
        (AlgEquiv.restrictNormalHom F g) x) }

/-- The literal finite-stage class quotient with its original global Galois action. -/
def arithmeticGlobalSPlaceStageQuotient
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    arithmeticGlobalSPlaceStageRep K Ω a ha F ⟶ arithmeticGlobalSPlaceClassStageRep K Ω a ha F :=
  Rep.ofHom {
    toLinearMap := (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom.toLinearMap
    isIntertwining' := fun g => LinearMap.ext (fun x =>
      Rep.hom_comm_apply (arithmeticSPlaceFiniteStageQuotient K Ω a ha F)
        (AlgEquiv.restrictNormalHom F g) x) }

private theorem principal_natural
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    arithmeticGlobalSUnitStageTransition K Ω a ha E F hEF ≫ arithmeticGlobalSPlaceStagePrincipal K Ω a ha F =
      arithmeticGlobalSPlaceStagePrincipal K Ω a ha E ≫ arithmeticGlobalSPlaceStageTransition K Ω a ha E F hEF := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (arithmeticSPlaceFiniteTransition_principal K Ω a ha E F hEF x).symm

private theorem quotient_natural
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    arithmeticGlobalSPlaceStageTransition K Ω a ha E F hEF ≫ arithmeticGlobalSPlaceStageQuotient K Ω a ha F =
      arithmeticGlobalSPlaceStageQuotient K Ω a ha E ≫ arithmeticGlobalSPlaceClassStageTransition K Ω a ha E F hEF := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (arithmeticSPlaceClassFiniteTransition_quotient K Ω a ha E F hEF x).symm

variable [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The original equivariant diagonal on the actual arithmetic coefficient colimits. -/
def arithmeticSPlaceColimitPrincipalRepHom :
    arithmeticSUnitCoefficientColimitRep K Ω a ha ⟶ arithmeticSPlaceColimitRep K Ω a ha :=
  coefficientRepresentationColimitMap _ _ _ _
    (arithmeticGlobalSPlaceStagePrincipal K Ω a ha) (principal_natural K Ω a ha)

/-- The original equivariant quotient on the actual arithmetic coefficient colimits. -/
def arithmeticSPlaceColimitQuotientRepHom :
    arithmeticSPlaceColimitRep K Ω a ha ⟶ arithmeticSPlaceClassColimitRep K Ω a ha :=
  coefficientRepresentationColimitMap _ _ _ _
    (arithmeticGlobalSPlaceStageQuotient K Ω a ha) (quotient_natural K Ω a ha)

/-- The equivariant diagonal is the same original coefficient map already proved injective. -/
theorem arithmeticSPlaceColimitPrincipalRepHom_toLinearMap :
    (arithmeticSPlaceColimitPrincipalRepHom K Ω a ha).hom.toLinearMap =
      arithmeticSPlaceColimitPrincipal K Ω a ha := rfl

/-- The equivariant quotient is the same original coefficient map already proved exact and onto. -/
theorem arithmeticSPlaceColimitQuotientRepHom_toLinearMap :
    (arithmeticSPlaceColimitQuotientRepHom K Ω a ha).hom.toLinearMap =
      arithmeticSPlaceColimitQuotient K Ω a ha := rfl

end
end Dubon2026
