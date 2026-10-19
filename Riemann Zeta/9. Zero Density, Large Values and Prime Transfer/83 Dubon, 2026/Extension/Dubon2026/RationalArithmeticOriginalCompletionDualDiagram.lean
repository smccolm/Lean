import Dubon2026.RationalArithmeticOriginalCompletionHomMap
import Dubon2026.GaloisTowerLocalUnitRelationCup

/-! The actual completion comparison of local dual relation sequences.
All three terms retain their original coefficients and linear maps;
the diagram serves DUB-17's prescribed local-class recovery. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra
  arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois



variable (a : 𝓞 ℚ)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)

variable (B : Rep.{0} ℤ Gal(F/ℚ))

/-- The literal completion-group change commutes with both maps of the
original local dual relation sequence. -/
def rationalArithmeticOriginalCompletionDualDiagram :
    (arithmeticPrimeLocalUnitDualSequence a F B p hp).map
      (Rep.resFunctor (rationalOriginalCompletionGaloisEquiv p hp).symm.toMonoidHom) ⟶
    originalContravariantHomShortComplex (galoisTowerLocalRelationComplex ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) B)
      (Rep.ofAlgebraAutOnUnits ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
        (rationalPrimeLocalClosure p hp)) where
  τ₁ := rationalArithmeticOriginalCompletionHomMap a F p hp B
  τ₂ := rationalArithmeticOriginalCompletionHomMap a F p hp (Rep.free ℤ Gal(F/ℚ) B)
  τ₃ := rationalArithmeticOriginalCompletionHomMap a F p hp (originalRelationModule B)
  comm₁₂ := rfl
  comm₂₃ := rfl

end
end Dubon2026
