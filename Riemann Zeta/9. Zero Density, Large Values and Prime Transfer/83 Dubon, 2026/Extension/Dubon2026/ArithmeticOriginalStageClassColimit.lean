import Dubon2026.OriginalUnramifiedStageInUnion
import Dubon2026.OriginalGaloisRestrictionTowerIso
import Dubon2026.ArithmeticClassesModOutsideColimit
import Dubon2026.OriginalRationalExceptionalClassTransition

/-! # The original scalar-stage class coefficient in the arithmetic colimit

Realize the same original stage inside the union, apply the literal
exceptional-class base change, and use its canonical colimit inclusion.
The tower isomorphism preserves coefficient values. This is the actual
coefficient map needed for DUB-17's enlarged-stage source-cup comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.Quotient.module
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union's displayed rational algebra. -/
local instance originalStageClassUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the displayed rational algebra of every original finite stage. -/
local instance originalStageClassFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)

/-- The actual full idele class quotient modulo units outside the original
exceptional support at the scalar-criterion stage. -/
abbrev arithmeticOriginalStageClassRep :=
  originalIdeleClassesModOutsideRep ℚ L.val
    (originalExceptionalIntegerSupport L.val (algebraMap (𝓞 ℚ) (𝓞 L.val) a)
      (originalIntegerMap_ne_zero (L := L.val) a ha))
    (originalExceptionalIntegerSupport_galoisStable L.val ℚ a ha)

/-- The same original class coefficient with its literal arithmetic Galois action. -/
abbrev arithmeticOriginalStageGlobalClassRep := by
  letI : Algebra L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  exact Rep.res (AlgEquiv.restrictNormalHom L.val :
    Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(L.val/ℚ))
      (arithmeticOriginalStageClassRep Ω a ha L)

/-- The original exceptional-class map to the literal image stage in the union. -/
def arithmeticOriginalStageClassToImage :
    let M := originalUnramifiedStageInUnion a L
    let e := originalUnramifiedStageInUnionEquiv a L
    letI : Algebra L.val M := e.toAlgHom.toAlgebra
    letI : Module L.val M := e.toAlgHom.toAlgebra.toModule
    letI : SMul L.val M := e.toAlgHom.toAlgebra.toSMul
    letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom e.toAlgHom
    Rep.res (AlgEquiv.restrictNormalHom L.val : Gal(M/ℚ) →* Gal(L.val/ℚ))
      (arithmeticOriginalStageClassRep Ω a ha L) ⟶
        arithmeticClassesModOutsideStageRep ℚ Ω a ha M := by
  let M := originalUnramifiedStageInUnion a L
  let e := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra L.val M := e.toAlgHom.toAlgebra
  letI : Module L.val M := e.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := e.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom e.toAlgHom
  exact originalRationalExceptionalClassTransition L.val M a ha

/-- Include the scalar stage's actual class quotient in the original
arithmetic class colimit, through its literal finite image. -/
def arithmeticOriginalStageClassToColimit :
    arithmeticOriginalStageGlobalClassRep Ω a ha L ⟶ arithmeticClassesModOutsideColimitRep ℚ Ω a ha := by
  let U := originalUnramifiedGaloisUnion (Ω := Ω) a
  let M := originalUnramifiedStageInUnion a L
  let e := originalUnramifiedStageInUnionEquiv a L
  letI : Algebra L.val M := e.toAlgHom.toAlgebra
  letI : Module L.val M := e.toAlgHom.toAlgebra.toModule
  letI : SMul L.val M := e.toAlgHom.toAlgebra.toSMul
  letI : IsScalarTower ℚ L.val M := IsScalarTower.of_algHom e.toAlgHom
  letI : Algebra L.val U :=
    (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L)).toAlgebra
  letI : IsScalarTower ℚ L.val U :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (originalUnramifiedGaloisStage_le_union a L))
  letI : IsScalarTower L.val M U := IsScalarTower.of_algebraMap_eq' rfl
  let π : Gal(U/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
  exact (originalGaloisRestrictionTowerIso ℚ L.val M U (arithmeticOriginalStageClassRep Ω a ha L)).inv ≫
    (Rep.resFunctor π).map (arithmeticOriginalStageClassToImage Ω a ha L) ≫
      coefficientRepresentationColimitOf _ (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha) M

/-- The global inclusion retains the literal exceptional-class base change
followed by the canonical finite-stage colimit value. -/
theorem arithmeticOriginalStageClassToColimit_apply (x : arithmeticOriginalStageGlobalClassRep Ω a ha L) :
    (arithmeticOriginalStageClassToColimit Ω a ha L).hom x =
      (coefficientRepresentationColimitOf _ (arithmeticGlobalClassesModOutsideStageTransition ℚ Ω a ha)
        (originalUnramifiedStageInUnion a L)).hom
          ((arithmeticOriginalStageClassToImage Ω a ha L).hom x) := rfl

end
end Dubon2026
