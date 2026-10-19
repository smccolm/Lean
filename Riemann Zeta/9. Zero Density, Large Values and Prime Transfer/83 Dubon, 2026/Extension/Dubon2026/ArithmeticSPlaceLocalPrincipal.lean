import Dubon2026.ArithmeticSPlaceLocalMap
import Dubon2026.ArithmeticSUnitLocalMap
import Dubon2026.ArithmeticSUnitFiniteStageInclusion

/-! The finite S-place principal map has exactly the same original local
value as the global S-unit inclusion. This connects DUB-17's actual finite
correction equation to its already constructed global connecting class. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticUnitMapAlgebra
  arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalExceptionalIndexedPrimeLiesOver

variable (a : 𝓞 ℚ) (ha : a ≠ 0)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : rationalArithmeticExceptionalPrimes a ha)

/-- The actual finite principal S-place image localizes to the same unit
as its actual global arithmetic S-unit image. -/
theorem rationalArithmeticSPlaceLocalMap_principal
    (u : arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) :
    rationalArithmeticSPlaceLocalMap a ha F p
      ((arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F).hom u) =
    rationalArithmeticSUnitLocalMap a ha p.val.val p.val.property
      ((arithmeticSUnitFiniteStageInclusion ℚ (AlgebraicClosure ℚ) a ha F).hom u) := by
  apply Additive.toMul.injective
  apply Units.ext
  let W := (rationalArithmeticOriginalPrime a p.val.val p.val.property F).adicCompletion F
  let Ω := rationalPrimeLocalClosure p.val.val p.val.property
  change algebraMap W Ω (algebraMap F W u.toMul.val.val) =
    rationalArithmeticLocalEmbedding (K := Ω) a
      (arithmeticSUnitFiniteStageUnitMap ℚ (AlgebraicClosure ℚ) a ha F u.toMul).val.val
  exact (rationalArithmeticOriginalCompletion_global a p.val.val p.val.property F u.toMul.val.val).trans
    (congrArg (rationalArithmeticLocalEmbedding (K := Ω) a)
      (arithmeticSUnitFiniteStageUnitMap_coe ℚ (AlgebraicClosure ℚ) a ha F u.toMul)).symm

end
end Dubon2026
