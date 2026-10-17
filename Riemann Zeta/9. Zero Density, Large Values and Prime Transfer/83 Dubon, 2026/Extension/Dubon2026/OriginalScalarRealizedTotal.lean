import Dubon2026.OriginalScalarSylowRealizationDegree
import Dubon2026.ArithmeticAllPrimeInfiniteKernelClassSystem

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup
variable (a : 𝓞 ℚ)

/-- Retain the original finite stage's displayed rational algebra. -/
local instance scalarRealizedTotalFiniteAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- Preserve the displayed rational algebra on the fixed-field image. -/
local instance scalarRealizedTotalIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (F : IntermediateField ℚ V) : Algebra ℚ F := F.algebra'

/-- The canonical original-prime idele total on the literal realized
fixed-field extension. Its field, inclusion and Galois structure are
constructed from the same original stage. -/
def originalScalarRealizedIdeleTotal
    (L : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a)
    (S : Subgroup Gal(L.val/ℚ)) :=
  let F := originalScalarFixedFieldInUnion (AlgebraicClosure ℚ) a L S
  let M := (originalUnramifiedStageInUnion a L).toIntermediateField
  let hFM := originalScalarFixedFieldInUnion_le (AlgebraicClosure ℚ) a L S
  let eK := originalScalarFixedFieldInUnionEquiv (AlgebraicClosure ℚ) a L S
  letI : FiniteDimensional ℚ F := eK.toLinearEquiv.finiteDimensional
  letI : FiniteDimensional ℚ M := (originalUnramifiedStageInUnion a L).finiteDimensional
  letI : Algebra F M := (IntermediateField.inclusion hFM).toAlgebra
  letI : Module F M := (IntermediateField.inclusion hFM).toAlgebra.toModule
  letI : SMul F M := (IntermediateField.inclusion hFM).toAlgebra.toSMul
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom (IntermediateField.inclusion hFM)
  letI : FiniteDimensional F M := FiniteDimensional.right ℚ F M
  letI : IsGalois F M := IsGalois.tower_top_of_isGalois ℚ F M
  rationalArithmeticRelativeStageIdeleTotalInvariant a F M hFM

end
end Dubon2026
