import Dubon2026.RationalTraceExceptionalSPlaceClassRecovery
import Dubon2026.RationalTraceExceptionalCartierFiniteSUnitCorrection

/-! Consume the actual source annihilator and finite correction theorem.
Every assembled source-field local class is now identified with its
prescribed coherent trace-dual class, retaining the very same finite
correction for the global construction on DUB-17's reverse-localization chain. -/
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

/-- The actual source-field classes and the same returned finite correction. -/
abbrev RationalTraceExceptionalRecoveredCorrectionResult : Prop :=
    ∃ N : OriginalUnramifiedGaloisStage (Ω := AlgebraicClosure ℚ) a,
      ∃ i : F →ₐ[ℚ] N.val,
      ∃ hi : ∀ x : F, (i x : AlgebraicClosure ℚ) = (x.val : AlgebraicClosure ℚ),
    let M := originalUnramifiedStageInUnion a N
    let hFM := originalUnramifiedStageInUnion_contains_embedded a F N i hi
    let hkerM := finiteStageCoefficientKernel_mono
      (rationalArithmeticTraceZeroIntegerRep a q σ) F M hFM hker
    let S := originalExceptionalIntegerSupport M (algebraMap (𝓞 ℚ) (𝓞 M) a)
      (originalIntegerMap_ne_zero (L := M) a ha)
    let hS := originalExceptionalIntegerSupport_galoisStable M ℚ a ha
    let B := rationalTraceOriginalFiniteRep a q σ M hkerM
    let v := rationalExceptionalIndexedBasePrime a ha
    let w := rationalExceptionalIndexedUpperPrime a ha M
    ∃ ψ : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Rep.res (originalAdicCompletionGaloisInclusion ℚ M (v p) (w p).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits ((v p).adicCompletion ℚ) ((w p).val.adicCompletion M),
      (∀ p : rationalArithmeticExceptionalPrimes a ha,
        rationalTraceExceptionalSPlaceLocalDualClass a ha q σ M hkerM hσ hn ψ p =
          rationalPrimeTraceUnitH1Equiv p.val.val p.val.property q
            (σ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property))
            (hσ.comp (rationalPrimeArithmeticRestriction a p.val.val p.val.property).continuous) hn
            (rationalArithmeticLocalNormalizationScalar a q hqa p.val.val p.val.property •
              rationalTraceExceptionalSourceH1 a ha q σ hσ d p)) ∧
      let Φ := originalIndexedPrimeSPlaceRelation ℚ M S hS
        (rationalArithmeticExceptionalPrimes a ha) w B
        (fun p => originalAdicUnitRelationMorphism ℚ M (v p) (w p).val B (ψ p))
      ArithmeticOriginalImageFiniteSUnitCorrectionResult (AlgebraicClosure ℚ) a ha N B Φ


/-- Source annihilation constructs the finite correction and proves the
prescribed identity for every actual assembled source-field local class. -/
theorem rationalTraceExceptional_exists_recovered_finite_correction
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    RationalTraceExceptionalRecoveredCorrectionResult a ha q σ F hker hn d hσ hqa := by
  have h := rationalTraceExceptionalCartier_exists_finite_SUnit_correction
    a ha q σ F hker hn d hσ hqa hq2 hann
  unfold RationalTraceExceptionalCartierFiniteCorrectionResult at h
  obtain ⟨N, i, hi, h⟩ := h
  unfold RationalTraceExceptionalRecoveredCorrectionResult
  refine ⟨N, i, hi, ?_⟩
  intro M hFM hkerM S hS B v w
  obtain ⟨ψ, hlocal, hcorrection⟩ := h
  refine ⟨ψ, ?_, hcorrection⟩
  intro p
  exact rationalTraceExceptionalSPlaceLocalDualClass_eq_coherent
    a ha q σ M hkerM hσ hn ψ p hqa (d p) (hlocal p)

end
end Dubon2026
