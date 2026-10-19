import Dubon2026.ArithmeticFiniteSUnitPrincipalConnecting
import Dubon2026.ArithmeticFiniteSUnitLocalCorrectionClass

/-! The actual finite correction equation identifies the localization
of its global connecting class with the S-place relation's local dual
class. This consumes the principal comparison and free-correction theorem
on DUB-17's direct construction of prescribed global restrictions. -/
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

variable (B : Rep.{0} ℤ Gal(F/ℚ)) [Finite B]

attribute [local instance] arithmeticLocalConnectingAlgebraicClosure
variable (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a) (hCoeff : ∀ b : B, q • b = 0)

/-- The actual finite correction gives the same localized H1 class as
the original S-place relation, with the free correction discharged. -/
theorem arithmeticFiniteCorrection_local_class
    (φ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (l : Rep.free ℤ Gal(F/ℚ) B ⟶ ArithmeticSPlaceFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (η : originalRelationModule B ⟶ arithmeticSUnitFiniteStageRep ℚ (AlgebraicClosure ℚ) a ha F)
    (hη : η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ (AlgebraicClosure ℚ) a ha F =
      φ - originalRelationInclusion B ≫ l) :
    let π := (AlgEquiv.restrictNormalHom F : rationalArithmeticGaloisGroup a →* Gal(F/ℚ)).comp
      (rationalPrimeArithmeticRestriction a p.val.val p.val.property).toMonoidHom
    let φp := (Rep.resFunctor π).map φ ≫ rationalArithmeticSPlaceLocalMorphism a ha F p
    arithmeticFiniteSUnitLocalH1Map a ha F B p.val.val p.val.property
      (arithmeticFiniteSUnitDualConnectingClass ℚ (AlgebraicClosure ℚ) a ha q hqa F B hCoeff η) =
      arithmeticPrimeLocalUnitDualConnecting a F B p.val.val p.val.property q hCoeff
        ((Representation.linHom.invariantsEquivRepHom _ _).symm φp) :=
  (arithmeticFiniteSUnitLocalH1Map_connecting_principal a ha F p B q hqa hCoeff η).trans
    (arithmeticFiniteSUnitCorrection_local_connecting a ha F B q hCoeff p φ l η hη)

end
end Dubon2026
