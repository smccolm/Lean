import Dubon2026.RationalTraceExceptionalCartierOriginalExtension
import Dubon2026.ArithmeticOriginalStageImageSUnitCorrection

/-! The actual coherent annihilator constructs a finite S-unit correction
of the very same Cartier relation with all local cup identities retained.
This discharges the finite correction input to DUB-17 reverse H1 localization;
the subsequent global cohomology construction and local recovery remain. -/
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

local instance rationalTraceFiniteCorrectionAlgebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
  have hAlg : @AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ) =
      (inferInstance : Algebra ℚ (AlgebraicClosure ℚ)) := Subsingleton.elim _ _
  have h := AlgebraicClosure.instIsAlgClosure ℚ
  rw [hAlg] at h
  exact h

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


/-- The actual Cartier family and a finite S-unit correction of its
indexed relation, without a supplied class extension or source-class lift. -/
abbrev RationalTraceExceptionalCartierFiniteCorrectionResult : Prop :=
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
      let Φ := originalIndexedPrimeSPlaceRelation ℚ M S hS
        (rationalArithmeticExceptionalPrimes a ha) w B
        (fun p => originalAdicUnitRelationMorphism ℚ M (v p) (w p).val B (ψ p))
      ArithmeticOriginalImageFiniteSUnitCorrectionResult (AlgebraicClosure ℚ) a ha N B Φ

/-- Original coherent source annihilation constructs a finite original
S-unit correction of the same local Cartier relation family. -/
theorem rationalTraceExceptionalCartier_exists_finite_SUnit_correction
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    RationalTraceExceptionalCartierFiniteCorrectionResult a ha q σ F hker hn d hqa := by
  classical
  unfold RationalTraceExceptionalCartierFiniteCorrectionResult
  have h := rationalTraceExceptionalCartier_exists_original_extension
    a ha q σ F hker hn d hσ hqa hq2 hann
  unfold RationalTraceExceptionalCartierExtensionResult at h
  obtain ⟨N, i, hi, h⟩ := h
  refine ⟨N, i, hi, ?_⟩
  intro M hFM hkerM S hS B v w
  obtain ⟨ψ, hlocal, f, hf⟩ := h
  refine ⟨ψ, hlocal, ?_⟩
  intro Φ
  have hB (b : B) : q • b = 0 := by
    simpa only [natCast_zsmul] using rationalArithmeticTraceZeroIntegerRep_prime_annihilates a q σ b
  exact arithmeticOriginalStageImage_exists_finite_SUnit_correction
    (AlgebraicClosure ℚ) a ha N q hqa B hB Φ f hf

end
end Dubon2026
