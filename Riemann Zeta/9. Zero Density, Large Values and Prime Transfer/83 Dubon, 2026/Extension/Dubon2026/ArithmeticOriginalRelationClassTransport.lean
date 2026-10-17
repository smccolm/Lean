import Dubon2026.ArithmeticOriginalRelationStagePlacement
import Dubon2026.OriginalRationalExceptionalClassTransition
import Dubon2026.OriginalRelationGroupChange

/-! # Literal relation and class transport to the embedded original stage

The descended relation morphism uses its actual finite field in the
arithmetic union. The canonical relation restriction and original full
class base change carry it through the constructed ambient embedding.
These are the exact coefficient maps needed to apply DUB-17's scalar
criterion to the actual source-class cocycle representative.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original arithmetic union inclusion. -/
local instance relationTransportUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual original finite field inclusion. -/
local instance relationTransportStageAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

variable (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[ℚ] F.val)
  (B : Rep.{0} ℤ Gal(P/ℚ))

/-- Transport the actual relation morphism by the literal Galois map and
the original exceptional-support full-class quotient base change. -/
def arithmeticOriginalStageRelationClassTransport
    (φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha P) :
    originalRelationModule (arithmeticOriginalStageRestrictedCoefficient Ω a P F i B) ⟶
      originalIdeleClassesModOutsideRep ℚ F.val
        (originalExceptionalIntegerSupport F.val (algebraMap (𝓞 ℚ) (𝓞 F.val) a)
          (originalIntegerMap_ne_zero (L := F.val) a ha))
        (originalExceptionalIntegerSupport_galoisStable F.val ℚ a ha) := by
  letI : Algebra P F.val := i.toAlgebra
  letI : Module P F.val := i.toAlgebra.toModule
  letI : SMul P F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
  let π : Gal(F.val/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
  exact originalRelationGroupChange π B ≫ (Rep.resFunctor π).map φ ≫
    originalRationalExceptionalClassTransition P F.val a ha

/-- The original relation transport has exactly the pointwise canonical
restriction followed by the original full-class base change. -/
theorem arithmeticOriginalStageRelationClassTransport_apply
    (φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha P) :
    letI : Algebra P F.val := i.toAlgebra
    letI : Module P F.val := i.toAlgebra.toModule
    letI : SMul P F.val := i.toAlgebra.toSMul
    letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
    let π : Gal(F.val/ℚ) →* Gal(P/ℚ) := AlgEquiv.restrictNormalHom P
    ∀ r, (arithmeticOriginalStageRelationClassTransport Ω a ha P F i B φ).hom r =
      (originalRationalExceptionalClassTransition P F.val a ha).hom
        (φ.hom ((originalRelationGroupChange π B).hom r)) := by
  intros
  rfl

/-- Carry the same actual relation through the embedded stage and the
constructed enlarged original stage using the two literal class maps. -/
def arithmeticOriginalEnlargedRelationClassTransport
    (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hFN : F.val.toIntermediateField ≤ N.val.toIntermediateField)
    (φ : originalRelationModule B ⟶ arithmeticClassesModOutsideStageRep ℚ Ω a ha P) :
    letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
    letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
    let τ : Gal(N.val/ℚ) →* Gal(F.val/ℚ) := AlgEquiv.restrictNormalHom F.val
    originalRelationModule (Rep.res τ (arithmeticOriginalStageRestrictedCoefficient Ω a P F i B)) ⟶
      originalIdeleClassesModOutsideRep ℚ N.val
        (originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha))
        (originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha) := by
  letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
  let τ : Gal(N.val/ℚ) →* Gal(F.val/ℚ) := AlgEquiv.restrictNormalHom F.val
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
  exact originalRelationGroupChange τ BF ≫
    (Rep.resFunctor τ).map (arithmeticOriginalStageRelationClassTransport Ω a ha P F i B φ) ≫
      originalRationalExceptionalClassTransition F.val N.val a ha

end
end Dubon2026
