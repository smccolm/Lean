import Dubon2026.RationalTraceOriginalSourceRestriction
import Dubon2026.RationalTraceSourceIntegerCocycle
import Dubon2026.RationalTracePrimeIntegerCocycle
import Dubon2026.GaloisTowerLocalH1AlgebraicComparison
/-! Identify the actual source restriction with the local class used in
the finite Cartier relation. The original cocycle values and the existing
continuous-to-algebraic H1 map supply this comparison for DUB-17. -/
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

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (hker : ∀ u : rationalArithmeticGaloisGroup a,
    AlgEquiv.restrictNormalHom F u = 1 →
    ∀ x : rationalArithmeticTraceZeroIntegerRep a q σ,
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ u x = x)
  (p : ℕ) (hp : p.Prime)

attribute [local instance] primeTraceIntegerContinuousSMul
  traceOriginalCoefficientTopology traceOriginalCoefficientDiscrete traceOriginalCoefficientContinuousSMul
  localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete
  localRelationCupCoefficientContinuousSMul

variable (hσ : Continuous σ)

attribute [local instance] rationalTraceCompletionCoefficientTopology
  rationalTraceCompletionCoefficientDiscrete traceFiniteSourceContinuousSMul

/-- Forgetting continuity of the transported source cocycle gives its
original arithmetic restriction through the actual coefficient map. -/
theorem rationalTraceOriginalSourceCocycle_toAlgebraic
    (c : continuousTraceZeroAdjointCocycles σ) :
    @continuousH1ToAlgebraic ℤ
      Gal(rationalPrimeLocalClosure p hp / (rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      _ _ _ _ (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
      (traceOriginalCoefficientTopology a q σ F hker p hp) _ _
      (by
        letI : TopologicalSpace (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp) :=
          traceOriginalCoefficientTopology a q σ F hker p hp
        letI : DiscreteTopology (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp) :=
          traceOriginalCoefficientDiscrete a q σ F hker p hp
        exact galoisTowerRestrictedCoefficientAction_continuous
          ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
          ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
          Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
            (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))
      (Quotient.mk _ (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp
        (rationalTracePrimeIntegerCocycle a q σ p hp c))) =
    groupCohomology.map (rationalTraceOriginalSourceRestriction a p hp)
      (rationalTraceOriginalSourceCoefficientMap a q σ F hker p hp) 1
      (continuousH1ToAlgebraic (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceIntegerAction_continuous a q σ hσ)
        (rationalArithmeticTraceIntegerH1Equiv a q σ hσ (Quotient.mk _ c))) := by
  change groupCohomology.H1π (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
      (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp
        (rationalTracePrimeIntegerCocycle a q σ p hp c)).val =
    groupCohomology.map (rationalTraceOriginalSourceRestriction a p hp)
      (rationalTraceOriginalSourceCoefficientMap a q σ F hker p hp) 1
      (groupCohomology.H1π (rationalArithmeticTraceZeroIntegerRep a q σ)
        (rationalTraceSourceIntegerCocycle a q σ c).val)
  refine Eq.trans ?_ (groupCohomology.H1π_comp_map_apply
    (A := rationalArithmeticTraceZeroIntegerRep a q σ)
    (B := rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp)
    (rationalTraceOriginalSourceRestriction a p hp)
    (rationalTraceOriginalSourceCoefficientMap a q σ F hker p hp)
    (rationalTraceSourceIntegerCocycle a q σ c).val).symm
  apply congrArg (groupCohomology.H1π (rationalTraceOriginalLocalCoefficientRep a q σ F hker p hp))
  apply Subtype.ext
  funext g
  rfl

end
end Dubon2026

