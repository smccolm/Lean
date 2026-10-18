import Dubon2026.RationalTraceExceptionalCartierTotalZero
import Dubon2026.ArithmeticSPlaceRelationTotalCriterion

/-! The actual coherent source annihilator constructs a class relation with zero obstruction. DUB-17 can feed this map equality, together with the same witness's local cup identities, to the constructed original extension criterion. -/
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


/-- The constructed Cartier relation has zero original class obstruction;
its prime annihilator is derived from the original trace coefficients. -/
theorem rationalTraceExceptionalCartier_exists_relation_obstruction_zero
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    let S := originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha)
    let hS := originalExceptionalIntegerSupport_galoisStable F ℚ a ha
    let B := rationalTraceOriginalFiniteRep a q σ F hker
    let v := rationalExceptionalIndexedBasePrime a ha
    let w := rationalExceptionalIndexedUpperPrime a ha F
    ∃ ψ : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Rep.res (originalAdicCompletionGaloisInclusion ℚ F (v p) (w p).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits ((v p).adicCompletion ℚ) ((w p).val.adicCompletion F),
      (∀ (p : rationalArithmeticExceptionalPrimes a ha)
        (z : galoisTowerLocalCoefficientH1 ((v p).adicCompletion ℚ)
          ((w p).val.adicCompletion F) (rationalPrimeLocalClosure p.val.val p.val.property)
          Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (v p) (w p).val) B),
        galoisTowerLocalUnitCup ((v p).adicCompletion ℚ) ((w p).val.adicCompletion F)
          (rationalPrimeLocalClosure p.val.val p.val.property) Gal(F/ℚ)
          (originalAdicCompletionGaloisInclusion ℚ F (v p) (w p).val) B
          (rationalTraceExceptionalIndexedCoherentCartierCocycle a ha q σ F hker hn d hqa p) z =
        galoisTowerLocalUnitRelationConnecting ((v p).adicCompletion ℚ)
          ((w p).val.adicCompletion F) (rationalPrimeLocalClosure p.val.val p.val.property)
          Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (v p) (w p).val) B (ψ p) z) ∧
      originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep ℚ F S hS)
        (originalIndexedPrimeSPlaceRelation ℚ F S hS
          (rationalArithmeticExceptionalPrimes a ha) w B
          (fun p => originalAdicUnitRelationMorphism ℚ F (v p) (w p).val B (ψ p)) ≫
          originalSPlaceIdeleClassRepHom ℚ F S hS ≫ originalSPlaceClassComparison ℚ F S hS) = 0 := by
  intro S hS B v w
  have ht := rationalTraceExceptionalCartier_exists_relation_total_zero a ha q σ F hker hn d hσ hqa hann
  with_reducible_and_instances
    obtain ⟨ψ, hlocal, htotal⟩ := ht
    refine ⟨ψ, hlocal, ?_⟩
  let Φ := originalIndexedPrimeSPlaceRelation ℚ F S hS
    (rationalArithmeticExceptionalPrimes a ha) w B
    (fun p => originalAdicUnitRelationMorphism ℚ F (v p) (w p).val B (ψ p))
  have hB (b : B) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact arithmeticSPlaceRelationObstruction_zero_of_total_zero a ha F B q hq2 hqa hB Φ y (htotal y)

end
end Dubon2026
