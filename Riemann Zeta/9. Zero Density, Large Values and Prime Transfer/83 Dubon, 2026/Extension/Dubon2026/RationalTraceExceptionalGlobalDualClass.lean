import Dubon2026.RationalTraceExceptionalCartierFiniteSUnitCorrection
import Dubon2026.RationalTraceFiniteCorrectionClassWitness

/-! The actual source annihilator supplies an original global trace-dual
H1 class together with its finite Cartier correction and all source-local
cup identities. These retained witnesses are the input to DUB-17 local
recovery; prescribed local restrictions are not asserted here. -/
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

local instance rationalTraceGlobalClassWitnessAlgebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
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


/-- The original global class and the actual Cartier data that construct it. -/
abbrev RationalTraceExceptionalGlobalClassWitness
    (x : RationalArithmeticTraceDualH1 a q hqa σ hσ) : Prop :=
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
      RationalTraceOriginalImageGlobalClassWitness a ha q σ N hkerM hσ hqa hn Φ x

/-- Source annihilation constructs an original global class, retaining
the same finite correction and every local Cartier cup identity. -/
theorem rationalTraceExceptional_exists_global_dual_class
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    ∃ x : RationalArithmeticTraceDualH1 a q hqa σ hσ,
      RationalTraceExceptionalGlobalClassWitness a ha q σ F hker hn d hσ hqa x := by
  classical
  have h := rationalTraceExceptionalCartier_exists_finite_SUnit_correction
    a ha q σ F hker hn d hσ hqa hq2 hann
  unfold RationalTraceExceptionalCartierFiniteCorrectionResult at h
  obtain ⟨N, i, hi, h⟩ := h
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
  obtain ⟨ψ, hlocal, hcorrection⟩ := h
  let Φ := originalIndexedPrimeSPlaceRelation ℚ M S hS
    (rationalArithmeticExceptionalPrimes a ha) w B
    (fun p => originalAdicUnitRelationMorphism ℚ M (v p) (w p).val B (ψ p))
  obtain ⟨x, hx⟩ := rationalTraceFiniteCorrection_exists_global_class
    a ha q σ N hkerM hσ hqa hn Φ hcorrection
  exact ⟨x, N, i, hi, ψ, hlocal, hx⟩

/-- The original global class chosen with its retained finite Cartier witness. -/
def rationalTraceExceptionalConstructedGlobalDualClass
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) : RationalArithmeticTraceDualH1 a q hqa σ hσ :=
  Classical.choose (rationalTraceExceptional_exists_global_dual_class
    a ha q σ F hker hn d hσ hqa hq2 hann)

/-- The constructed global class retains its actual source-local cup
identities and finite S-unit correction, rather than just nonemptiness. -/
theorem rationalTraceExceptionalConstructedGlobalDualClass_spec
    (hq2 : q ≠ 2)
    (hann : ∀ y : ContinuousTraceZeroAdjointH1 σ hσ,
      rationalArithmeticExceptionalTracePairing a q hqa ha σ hσ
        (rationalTraceExceptionalSourceH1 a ha q σ hσ d)
        (rationalArithmeticTraceH1Localization a q ha σ hσ y) = 0) :
    RationalTraceExceptionalGlobalClassWitness a ha q σ F hker hn d hσ hqa
      (rationalTraceExceptionalConstructedGlobalDualClass a ha q σ F hker hn d hσ hqa hq2 hann) :=
  Classical.choose_spec (rationalTraceExceptional_exists_global_dual_class
    a ha q σ F hker hn d hσ hqa hq2 hann)

end
end Dubon2026
