import Dubon2026.RationalTraceExceptionalCocycles
import Dubon2026.OriginalIndexedLocalCocycleRelationFamily

/-! Assemble the actual original exceptional-prime Cartier cocycles into
one original S-place relation. This is the finite-family construction
required before DUB-17's normalized canonical cup-total comparison. -/
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
S-place relation with every original local value and every local unit cup.
The prime support and distinct contractions are proved, not supplied. -/
theorem rationalTraceExceptionalCartierCocycles_exists_SPlace_relation :
    let c' := rationalTraceExceptionalCartierCocycle a ha q σ F hker hn c
    OriginalIndexedLocalCupFamilyRealization ℚ F
      (originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
        (originalIntegerMap_ne_zero (L := F) a ha))
      (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
      (rationalArithmeticExceptionalPrimes a ha)
      (rationalExceptionalIndexedBasePrime a ha) (rationalExceptionalIndexedUpperPrime a ha F)
      (fun p => rationalPrimeLocalClosure p.val.val p.val.property)
      (rationalTraceOriginalFiniteRep a q σ F hker) c' := by
  let c' := rationalTraceExceptionalCartierCocycle a ha q σ F hker hn c
  exact originalIndexedLocalCocycles_exists_SPlace_relation ℚ F
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

