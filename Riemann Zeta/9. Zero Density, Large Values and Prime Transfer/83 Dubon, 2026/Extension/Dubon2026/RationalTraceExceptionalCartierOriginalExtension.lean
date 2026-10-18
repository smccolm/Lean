import Dubon2026.RationalTraceExceptionalClassObstructionZero
import Dubon2026.RationalTraceOriginalConstructedExtension

/-! The original coherent annihilator constructs an actual relation
extension at the native arithmetic field, retaining the same local cup
witness. This joins DUB-17's canonical Cartier total, class obstruction and
constructed extension criterion before recovery of prescribed local H1. -/
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


/-- The exact original-stage Cartier extension conclusion, including
the same local cup family. This abbreviation changes no mathematical
condition; the following theorem constructs its witnesses. -/
abbrev RationalTraceExceptionalCartierExtensionResult : Prop :=
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
    let e := originalUnramifiedStageInUnionEquiv a N
    let BN := arithmeticOriginalStageRestrictedCoefficient (AlgebraicClosure ℚ) a M N
      e.symm.toAlgHom B
    let C := arithmeticOriginalStageClassRep (AlgebraicClosure ℚ) a ha N
    ∃ ψ : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Rep.res (originalAdicCompletionGaloisInclusion ℚ M (v p) (w p).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits ((v p).adicCompletion ℚ) ((w p).val.adicCompletion M),
      (∀ (p : rationalArithmeticExceptionalPrimes a ha)
        (z : galoisTowerLocalCoefficientH1 ((v p).adicCompletion ℚ)
          ((w p).val.adicCompletion M) (rationalPrimeLocalClosure p.val.val p.val.property)
          Gal(M/ℚ) (originalAdicCompletionGaloisInclusion ℚ M (v p) (w p).val) B),
        galoisTowerLocalUnitCup ((v p).adicCompletion ℚ) ((w p).val.adicCompletion M)
          (rationalPrimeLocalClosure p.val.val p.val.property) Gal(M/ℚ)
          (originalAdicCompletionGaloisInclusion ℚ M (v p) (w p).val) B
          (rationalTraceExceptionalIndexedCoherentCartierCocycle a ha q σ M hkerM hn d hqa p) z =
        galoisTowerLocalUnitRelationConnecting ((v p).adicCompletion ℚ)
          ((w p).val.adicCompletion M) (rationalPrimeLocalClosure p.val.val p.val.property)
          Gal(M/ℚ) (originalAdicCompletionGaloisInclusion ℚ M (v p) (w p).val) B (ψ p) z) ∧
      ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C,
        originalRelationInclusion BN ≫ f =
          arithmeticOriginalStageRelationClassTransport (AlgebraicClosure ℚ) a ha M N
            e.symm.toAlgHom B
            (originalIndexedPrimeSPlaceRelation ℚ M S hS
              (rationalArithmeticExceptionalPrimes a ha) w B
              (fun p => originalAdicUnitRelationMorphism ℚ M (v p) (w p).val B (ψ p)) ≫
                originalSPlaceIdeleClassRepHom ℚ M S hS ≫ originalSPlaceClassComparison ℚ M S hS)

/-- The coherent source annihilator yields an actual free-cover class
extension at a constructed original field, together with every local H1
cup identity for that same Cartier relation witness. -/
theorem rationalTraceExceptionalCartier_exists_original_extension
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    RationalTraceExceptionalCartierExtensionResult a ha q σ F hker hn d hqa := by
  unfold RationalTraceExceptionalCartierExtensionResult
  have hc := rationalTrace_exists_original_constructed_extension a ha q σ F hker hq2 hqa
  let N := Classical.choose hc
  have hN := Classical.choose_spec hc
  let i := Classical.choose hN
  have hi' := Classical.choose_spec hN
  let hi := Classical.choose hi'
  have hcriterion := Classical.choose_spec hi'
  refine ⟨N, i, hi, ?_⟩
  intro M hFM hkerM S hS B v w e BN C
  have hz := rationalTraceExceptionalCartier_exists_relation_obstruction_zero
    a ha q σ M hkerM hn d hσ hqa hq2 hann
  with_reducible_and_instances
    obtain ⟨ψ, hlocal, hzero⟩ := hz
    refine ⟨ψ, hlocal, ?_⟩
  exact hcriterion _ hzero

end
end Dubon2026
