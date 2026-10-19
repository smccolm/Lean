import Dubon2026.RationalTraceExceptionalRecoveredCorrection
import Dubon2026.RationalTraceExceptionalPrescribedRestriction

/-! Consume the actual annihilator-produced finite correction and every
proved source-local class identity to construct a single original global
trace-dual class with all the prescribed restrictions. This is the
reverse exceptional H1 localization input on DUB-17's Selmer chain. -/
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


include F hker hn in
/-- An original exceptional source family annihilating global classes is
the localization of an actual original global trace-dual H1 class. -/
theorem rationalTraceExceptionalSource_exists_global_class
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    ∃ x : RationalArithmeticTraceDualH1 a q hqa σ hσ,
      rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ x =
        rationalTraceExceptionalSourceH1 a ha q σ hσ d := by
  have h := rationalTraceExceptional_exists_recovered_finite_correction
    a ha q σ F hker hn d hσ hqa hq2 hann
  unfold RationalTraceExceptionalRecoveredCorrectionResult at h
  obtain ⟨N, i, hi, h⟩ := h
  let M := originalUnramifiedStageInUnion a N
  let hFM := originalUnramifiedStageInUnion_contains_embedded a F N i hi
  let hkerM := finiteStageCoefficientKernel_mono
    (rationalArithmeticTraceZeroIntegerRep a q σ) F M hFM hker
  obtain ⟨ψ, hlocal, hcorrection⟩ := h
  unfold ArithmeticOriginalImageFiniteSUnitCorrectionResult at hcorrection
  obtain ⟨L, hML, hcorrection⟩ := hcorrection
  letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
  letI : Module M L := Algebra.toModule
  letI : SMul M L := Algebra.toSMul
  obtain ⟨l, η, hη⟩ := hcorrection
  refine ⟨rationalTraceFiniteCorrectionDirectDualClass a ha q σ M L hML hkerM hσ hqa hn η, ?_⟩
  funext p
  change rationalPrimeCyclotomicAdjointH1Restriction a q hqa p.val.val p.val.property σ hσ
    (rationalTraceFiniteCorrectionDirectDualClass a ha q σ M L hML hkerM hσ hqa hn η) =
      rationalTraceExceptionalSourceH1 a ha q σ hσ d p
  exact rationalTraceExceptionalDirect_prescribed_restriction
    a ha q σ M hkerM hσ hn ψ p L hML hqa (rationalTraceExceptionalSourceH1 a ha q σ hσ d p) (hlocal p) l η hη

end
end Dubon2026
