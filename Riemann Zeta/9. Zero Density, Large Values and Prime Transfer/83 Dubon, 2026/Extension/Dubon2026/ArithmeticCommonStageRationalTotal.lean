import Dubon2026.OriginalSameUpperClassBaseChange
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant

/-! Express the canonical finite-prime total on the actual rational-base
idele H2 class returned by DUB-17's source-cup descent. The arithmetic
bottom field is used through its literal inclusion, with the original
full-class restriction explicitly retained. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (M : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The actual rational-base idele class, with only its base changed to
the arithmetic bottom field; the upper field and idele coefficients remain the same. -/
def arithmeticCommonStageIdeleToBottom :
    groupCohomology (originalFullIdeleRep ℚ M) 2 →+
      rationalArithmeticRelativeStageIdeleH2 a ⊥ M.toIntermediateField bot_le := by
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  letI : Algebra K M := (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := Algebra.toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom
    (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le))
  exact (originalFullIdeleBaseChangeH2 ℚ K M M).hom.toAddMonoidHom

/-- The canonical total of the same actual rational-base full-idele class. -/
def arithmeticCommonStageRationalIdeleTotal :
    groupCohomology (originalFullIdeleRep ℚ M) 2 →+ AddCircle (1 : ℚ) := by
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  letI : Algebra K M := (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := Algebra.toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom
    (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le))
  letI : IsGalois K M := IsGalois.tower_top_of_isGalois ℚ K M
  exact (rationalArithmeticRelativeStageIdeleTotalInvariant a K M.toIntermediateField bot_le).comp
    (arithmeticCommonStageIdeleToBottom a M)

/-- The literal bottom-field idele class has exactly the restriction of
the original full-class image, by the proved same-upper-field square. -/
theorem arithmeticCommonStageIdeleToBottom_class
    (x : groupCohomology (originalFullIdeleRep ℚ M) 2) :
    let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
    letI : Algebra K M := (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le)).toAlgebra
    letI : Module K M := Algebra.toModule
    letI : SMul K M := Algebra.toSMul
    letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom
      (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le))
    (groupCohomology.functor ℤ Gal(M/K) 2).map (originalFullClassRepHom K M)
      (arithmeticCommonStageIdeleToBottom a M x) =
      originalIdeleClassTowerH2Restriction ℚ K M
        ((groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M) x) := by
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  letI : Algebra K M := (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := Algebra.toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom
    (IntermediateField.inclusion (show K ≤ M.toIntermediateField from bot_le))
  exact originalFullIdeleBaseChangeH2_class_same_upper ℚ K M x

end
end Dubon2026
