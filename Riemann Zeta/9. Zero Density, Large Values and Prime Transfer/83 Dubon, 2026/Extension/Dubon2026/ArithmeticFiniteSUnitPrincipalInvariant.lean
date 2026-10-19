import Dubon2026.ArithmeticSPlaceLocalPrincipal
import Dubon2026.ArithmeticFiniteSUnitDualConnecting
import Dubon2026.ArithmeticFiniteSUnitLocalDualDiagram

/-! The locally mapped invariant of the actual finite S-unit relation
is the invariant of its principal S-place image. This is the concrete
entry bridge from the constructed global class into the finite correction
equation on DUB-17's prescribed-restriction chain. -/
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

variable (B : Rep.{0} ℤ Gal(F/ℚ))

/-- The native global connecting invariant and the actual principal
S-place projection have identical local relation values. -/
theorem arithmeticFiniteSUnitRelationInvariant_local_principal
    (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F) :
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let d := arithmeticFiniteSUnitLocalDualDiagram a ha F B p.val.val p.val.property
    let φ := (Rep.resFunctor π).map
      (η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F) ≫
        rationalArithmeticSPlaceLocalMorphism a ha F p
    d.τ₃.hom (arithmeticFiniteSUnitRelationInvariant ℚ (AlgebraicClosure ℚ) a ha F B η).val =
      φ.hom.toLinearMap := by
  intro π d φ
  apply LinearMap.ext
  intro x
  exact (rationalArithmeticSPlaceLocalMap_principal a ha F p (η.hom x)).symm

end
end Dubon2026
