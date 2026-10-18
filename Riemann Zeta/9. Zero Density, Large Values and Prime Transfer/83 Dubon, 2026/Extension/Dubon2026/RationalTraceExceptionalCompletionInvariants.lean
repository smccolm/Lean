import Dubon2026.RationalTraceExceptionalCocycles
import Dubon2026.OriginalIndexedLocalCocycleInvariantFamily

/-! The actual exceptional Cartier family constructs one S-place relation
whose completion invariants are the original local cup invariants on
constructed continuous lifts of every restricted global class. This
removes the local relation and H1-lift premises in DUB-17's total comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
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

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (hn : (Fintype.card ι : ZMod q) ≠ 0)
  (c : ∀ p : rationalArithmeticExceptionalPrimes a ha,
    rationalTraceOriginalCartierSourceCocycles a q σ p.val.val p.val.property)

attribute [local instance] traceExceptionalHomTopology traceExceptionalHomDiscrete
  traceExceptionalHomContinuousSMul indexedPrimeRelationCosets

/-- The actual exceptional-prime Cartier cocycles construct one original
S-place relation and prove its completion-invariant identities on constructed
finite continuous lifts of every restricted global H1 class. -/
theorem rationalTraceExceptionalCartierCocycles_exists_completion_invariants :
    let c' := rationalTraceExceptionalCartierCocycle a ha q σ F hker hn c
    OriginalIndexedLocalCupInvariantRealization ℚ F
      (originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha))
      (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
      (rationalArithmeticExceptionalPrimes a ha)
      (rationalExceptionalIndexedBasePrime a ha) (rationalExceptionalIndexedUpperPrime a ha F)
      (fun p => rationalPrimeLocalClosure p.val.val p.val.property)
      (rationalTraceOriginalFiniteRep a q σ F hker) c' := by
  let c' := rationalTraceExceptionalCartierCocycle a ha q σ F hker hn c
  exact originalIndexedLocalCocycles_exists_completion_invariants ℚ F
    (originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha))
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (rationalArithmeticExceptionalPrimes a ha)
    (rationalExceptionalIndexedBasePrime a ha) (rationalExceptionalIndexedUpperPrime a ha F)
    (fun p => rationalPrimeLocalClosure p.val.val p.val.property)
    (rationalTraceOriginalFiniteRep a q σ F hker)
    (rationalExceptionalIndexedBasePrime_injective a ha) c'

end
end Dubon2026

