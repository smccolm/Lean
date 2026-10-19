import Dubon2026.RationalTraceExceptionalRecoveredGlobalClass

/-! Reverse localization for the actual exceptional trace-dual H1
product. Existing finite-action descent and cocycle representatives feed
the proved annihilator-to-global construction. No splitting field,
finite correction, cup comparison or local identity is assumed. -/
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
/-- Every original exceptional dual class annihilating the global primal
image is the localization of one genuine original global dual class. -/
theorem rationalArithmeticTraceDualH1_exists_global_of_annihilator
    (hq2 : q ≠ 2)
    (x : RationalArithmeticExceptionalTraceDualH1 a q ha σ hσ)
    (hx : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ x
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    ∃ g : RationalArithmeticTraceDualH1 a q hqa σ hσ,
      rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ g = x := by
  obtain ⟨F, hker, _⟩ := rationalTrace_exists_finiteCompletion_action a q σ hσ
  obtain ⟨d, hd⟩ := rationalTraceExceptionalSourceH1_surjective a ha q σ hσ x
  have hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0 := by
    rw [hd]
    exact hx
  obtain ⟨g, hg⟩ := rationalTraceExceptionalSource_exists_global_class
    a ha q σ F hker hn d hσ hqa hq2 hann
  exact ⟨g, hg.trans hd⟩

include hn in
/-- The original dual localization image is exactly the annihilator of
the original primal image under the proved exceptional perfect pairing. -/
theorem rationalArithmeticTraceDualLocalization_range_eq_annihilator
    (hq2 : q ≠ 2) :
    LinearMap.range ((rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ).comp
      (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ)) =
        (LinearMap.range (rationalArithmeticTraceH1Localization a q ha σ hσ)).dualAnnihilator := by
  apply le_antisymm (rationalArithmeticTraceDualLocalization_range_le_annihilator a q hqa ha σ hσ hq2)
  intro f hf
  obtain ⟨x, hx⟩ := (rationalArithmeticExceptionalTracePairing_isPerfPair a q hqa ha σ hσ hn).bijective_left.surjective f
  have hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ x
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0 := by
    intro y
    rw [hx]
    exact (Submodule.mem_dualAnnihilator _).mp hf _ ⟨y, rfl⟩
  obtain ⟨g, hg⟩ := rationalArithmeticTraceDualH1_exists_global_of_annihilator
    a ha q σ hn hσ hqa hq2 x hann
  refine ⟨g, ?_⟩
  change rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
    (rationalArithmeticTraceDualH1Localization a q hqa ha σ hσ g) = f
  rw [hg, hx]

end
end Dubon2026
