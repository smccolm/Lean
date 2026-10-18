import Dubon2026.RationalTraceOriginalSourceClass
/-! Match every constructed finite local H1 lift to the actual original source restriction. This discharges the lift-comparison premise in DUB-17's Cartier cup-total assembly. -/
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


attribute [local instance 1100] finiteLocalRelationCoefficientTopology
  finiteLocalRelationCoefficientDiscrete finiteLocalRelationCoefficientContinuousSMul

/-- Every finite continuous lift inflates to the restriction of the same
original trace-zero source class, independently of the chosen lift. -/
theorem rationalTraceFiniteLocalH1Inflation_eq_source
    (y : groupCohomology (rationalTraceOriginalFiniteRep a q σ F hker) 1)
    (x : galoisTowerFiniteLocalCoefficientH1
      ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) Gal(F/ℚ)
      (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))
    (hx : @continuousH1ToAlgebraic ℤ
      Gal((rationalArithmeticOriginalPrime a p hp F).adicCompletion F /
        (rationalOriginalPrimePlace p hp).adicCompletion ℚ) _ _ _ _
      (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))
      ⊥ _ _ continuous_of_discreteTopology x =
      groupCohomology.map
        (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F))
        (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
          (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker))) 1 y)
    (c : continuousTraceZeroAdjointCocycles σ)
    (hc : @continuousH1ToAlgebraic ℤ (rationalArithmeticGaloisGroup a) _ _ _ _
      (rationalArithmeticTraceZeroIntegerRep a q σ)
      (rationalTraceCompletionCoefficientTopology a q σ) _ _
      (rationalTraceIntegerAction_continuous a q σ hσ)
      (rationalArithmeticTraceIntegerH1Equiv a q σ hσ (Quotient.mk _ c)) =
      groupCohomology.map (AlgEquiv.restrictNormalHom F)
        (rationalTraceFiniteSourceCoefficientMap a q σ F hker) 1 y) :
    galoisTowerFiniteLocalH1Inflation ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
      Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
        (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker) x =
      Quotient.mk _ (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp
        (rationalTracePrimeIntegerCocycle a q σ p hp c)) := by
  apply galoisTowerFiniteLocalH1Inflation_eq_restriction
    ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
    ((rationalArithmeticOriginalPrime a p hp F).adicCompletion F) (rationalPrimeLocalClosure p hp)
    Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (rationalOriginalPrimePlace p hp)
      (rationalArithmeticOriginalPrime a p hp F)) (rationalTraceOriginalFiniteRep a q σ F hker) y x hx
  exact (rationalTraceOriginalSourceCocycle_toAlgebraic a q σ F hker p hp hσ c).trans
    ((congrArg (fun t => groupCohomology.map (rationalTraceOriginalSourceRestriction a p hp)
      (rationalTraceOriginalSourceCoefficientMap a q σ F hker p hp) 1 t) hc).trans
        (rationalTraceFiniteSourceH1_original_restriction a q σ F hker p hp y))

end
end Dubon2026
