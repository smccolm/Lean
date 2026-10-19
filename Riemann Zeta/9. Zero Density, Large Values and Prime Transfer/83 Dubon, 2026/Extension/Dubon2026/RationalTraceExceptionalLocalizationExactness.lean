import Dubon2026.RationalTraceExceptionalReverseLocalization

/-! Exactness at the genuine exceptional primal H1 product. The proved
dual annihilator equality and pinned Mathlib's double-annihilator theorem
identify precisely the kernel of the original global-dual obstruction.
This is DUB-17's arithmetic H1 exactness input for dual Selmer/patching. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionTargetAlgebra arithmeticOrbitCompletionClosureAlgebra arithmeticOrbitCompletionGlobalAlgebra
  rationalOriginalCompletionTargetAlgebra rationalOriginalCompletionClosureAlgebra
  rationalOriginalCompletionClosureTower rationalOriginalCompletionGalois rationalArithmeticOriginalPrimeLiesOver
  originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  rationalArithmeticOriginalCompletion_closureTower rationalArithmeticOriginalFiniteGalois
  rationalTraceCompletionArithmeticGalois traceOriginalFiniteRepFinite rationalExceptionalIndexedPrimeLiesOver
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete originalAdicRelationCupHomContinuousSMul

attribute [local instance] rationalTraceFiniteCorrectionAlgebraicClosure

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  (d : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)

attribute [local instance] traceExceptionalHomTopology traceExceptionalHomDiscrete
  traceExceptionalHomContinuousSMul indexedPrimeRelationCosets


attribute [local instance] finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul
  localRelationCupUnitsTopology localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete
  indexedCoherentHomTopology indexedCoherentHomDiscrete indexedCoherentHomContinuousSMul

variable (hσ : Continuous σ) (hqa : (q : 𝓞 ℚ) ∣ a)


attribute [local instance 1100] Submodule.module Submodule.Quotient.module
attribute [local instance] finiteLocalPrimeHomTopology finiteLocalPrimeHomDiscrete
  finiteLocalPrimeHomContinuousSMul




include hn in
/-- The original global localization image equals the kernel of the
actual global-dual obstruction, with all reverse-localization inputs proved. -/
theorem rationalArithmeticTraceH1Localization_range_eq_obstruction_ker
    (hq2 : q ≠ 2) :
    LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) =
      LinearMap.ker (rationalArithmeticTraceH1GlobalObstruction a q hqa ha σ hσ) := by
  calc
    LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ) =
        (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ)).dualAnnihilator.dualCoannihilator :=
      Subspace.dualAnnihilator_dualCoannihilator_eq.symm
    _ = (LinearMap.range ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).comp
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ))).dualCoannihilator :=
      congrArg Submodule.dualCoannihilator
        (rationalArithmeticTraceDualLocalization_range_eq_annihilator a ha q σ hn hσ hqa hq2).symm
    _ = LinearMap.ker ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).comp
        (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)).flip :=
      LinearMap.dualCoannihilator_range_eq_ker_flip _
    _ = LinearMap.ker (rationalArithmeticTraceH1GlobalObstruction a q hqa ha σ hσ) := rfl

end
end Dubon2026
