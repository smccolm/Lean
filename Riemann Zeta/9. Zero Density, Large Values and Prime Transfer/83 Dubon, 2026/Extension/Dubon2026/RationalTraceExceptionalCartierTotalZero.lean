import Dubon2026.ArithmeticRationalIndexedCupTotal
import Dubon2026.RationalTraceExceptionalIndexedCupValue
import Dubon2026.RationalTraceExceptionalFiniteCupZero

/-! Assemble the original exceptional Cartier relation with its canonical rational total. This is the actual total-zero input to DUB-17's proved relation-obstruction criterion; the same witness retains every local cup identity for the later reverse-localization step. -/
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

/-- Coherent source orthogonality constructs one original exceptional
Cartier relation whose actual canonical total vanishes on every finite H1
input, retaining all local cup identities for that same relation. -/
theorem rationalTraceExceptionalCartier_exists_relation_total_zero
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
      ∀ y : groupCohomology B 1,
        arithmeticCommonStageRationalIdeleTotal a F
          ((groupCohomology.functor ℤ Gal(F/ℚ) 2).map (originalSPlaceFullIdeleInclusion ℚ F S hS)
            (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep ℚ F S hS)
              (originalIndexedPrimeSPlaceRelation ℚ F S hS
                (rationalArithmeticExceptionalPrimes a ha) w B
                (fun p => originalAdicUnitRelationMorphism ℚ F (v p) (w p).val B (ψ p))) y)) = 0 := by
  intro S hS B v w
  have h := arithmeticRationalIndexedLocalCocycles_exists_cup_total a F
    (originalExceptionalIntegerSupport F (algebraMap (𝓞 ℚ) (𝓞 F) a)
      (originalIntegerMap_ne_zero (L := F) a ha))
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (rationalArithmeticExceptionalPrimes a ha)
    (rationalExceptionalIndexedBasePrime a ha) (rationalExceptionalIndexedUpperPrime a ha F)
    (hLies := fun p => rationalExceptionalIndexedPrimeLiesOver a ha F p)
    (fun p => rationalPrimeLocalClosure p.val.val p.val.property)
    (hTower := fun p => rationalArithmeticOriginalCompletion_closureTower a p.val.val p.val.property F)
    (rationalTraceOriginalFiniteRep a q σ F hker)
    (rationalExceptionalIndexedBasePrime_injective a ha)
  let c : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      continuousRepresentationCocyclesOne
        (originalAdicLocalCoefficientUnitHom ℚ F (rationalExceptionalIndexedBasePrime a ha p)
          (rationalExceptionalIndexedUpperPrime a ha F p).val
          (rationalPrimeLocalClosure p.val.val p.val.property)
          (rationalTraceOriginalFiniteRep a q σ F hker)) :=
    rationalTraceExceptionalIndexedCoherentCartierCocycle a ha q σ F hker hn d hqa
  with_reducible_and_instances
    have hr := h c
  obtain ⟨ψ, hlocal, htotal⟩ := hr
  with_reducible_and_instances
    refine ⟨ψ, hlocal, fun y => ?_⟩
  obtain ⟨x, hx, hsum⟩ := htotal y
  have hpoint (p : rationalArithmeticExceptionalPrimes a ha) :=
    rationalTraceExceptionalCoherentFiniteCupValue_eq_indexed a ha q σ F hker hn d hqa p (x p)
  have hz := rationalTraceExceptionalFiniteCupSum_eq_zero a ha q σ F hker hn d hσ hqa hann y
  with_reducible_and_instances
    have hzero := hz x hx
  with_reducible_and_instances
    exact (hsum.trans (Finset.sum_congr rfl (fun p _ => hpoint p))).trans hzero

end
end Dubon2026
