import Dubon2026.RationalTraceOriginalLocalH1Cup
import Dubon2026.RationalPrimeTraceUnitCupSeparation

/-! Recover the prescribed prime-local class directly from the retained
original-completion cups of its actual image. Both classes already have
prime-local representatives in DUB-17; only the proved forward comparison
and existing perfect pairing are needed. -/
namespace Dubon2026
noncomputable section
private theorem eq_of_original_cup_tests
    {C Q U Z W : Type} (π : C → Q) (hπ : Function.Surjective π)
    (cup : Q → U → Z) (originalCup : C → U → W) (f : W → Z)
    (hc : ∀ c u, f (originalCup c u) = cup (π c) u)
    (hs : ∀ u v, (∀ z, cup z u = cup z v) → u = v)
    (u v : U) (h : ∀ c, originalCup c u = originalCup c v) : u = v := by
  apply hs
  intro z
  obtain ⟨c, rfl⟩ := hπ z
  exact (hc c u).symm.trans ((congrArg f (h c)).trans (hc c v))

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

attribute [local instance] traceOriginalFiniteRepFinite primeTraceIntegerContinuousSMul
  traceOriginalCoefficientTopology traceOriginalCoefficientDiscrete traceOriginalCoefficientContinuousSMul
  traceCartierOriginalHomTopology traceCartierOriginalHomDiscrete
  traceOriginalSourceHomContinuousSMul traceOriginalTargetHomTopology
  traceOriginalTargetHomDiscrete traceOriginalTargetHomContinuousSMul
  localRelationCupCoefficientTopology localRelationCupCoefficientDiscrete
  localRelationCupCoefficientContinuousSMul localRelationCupUnitsTopology
  localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul

variable (hσ : Continuous σ) (hn : (Fintype.card ι : ZMod q) ≠ 0)


/-- Retain the original discrete local roots-of-unity coefficient. -/
local instance mappedCupSeparationRootTopology : TopologicalSpace
    (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q) := ⊥
local instance mappedCupSeparationRootDiscrete : DiscreteTopology
    (galoisRootOfUnityRepresentation (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q) := ⟨rfl⟩

/-- Original source cups determine the two actual prime-local classes
through their checked completion images. The existing perfect pairing
and forward cup comparison discharge separation without a new premise. -/
theorem rationalTraceOriginalMappedHomH1_eq_of_cups
    (u v : ContinuousRepresentationH1 (rationalPrimeTraceUnitHomRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
      (rationalPrimeTraceUnitHomAction_continuous p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn))
    (h : ∀ c : continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))),
      rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp
        (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c))
        (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn u) =
      rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp
        (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c))
        (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn v)) : u = v := by
  let Q := ContinuousRepresentationH1 (rationalPrimeTraceZeroIntegerRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
    (rationalPrimeTraceIntegerAction_continuous p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous))
  let C := continuousRepresentationCocyclesOne (rationalPrimeTraceZeroIntegerRep p hp q
    (σ.comp (rationalPrimeArithmeticRestriction a p hp)))
  let π : C → Q := Submodule.Quotient.mk
  have hπ : Function.Surjective π := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ c => exact ⟨c, rfl⟩
  exact eq_of_original_cup_tests π hπ
    (fun z x => rationalPrimeTraceUnitEvaluationCup p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn z x)
    (fun c x => rationalTraceOriginalLocalUnitH1Cup a q σ F hker p hp
      (Submodule.Quotient.mk (rationalTraceOriginalCoefficientCocycle a q σ F hker p hp c))
      (rationalTraceOriginalLocalHomH1Equiv a q σ F hker p hp hσ hn x))
    (continuousGaloisUnitBaseChangeH2 ((rationalOriginalPrimePlace p hp).adicCompletion ℚ)
      (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp) (rationalPrimeLocalClosure p hp))
    (rationalTraceOriginalLocalUnitH1Cup_baseChange a q σ F hker p hp hσ hn)
    (fun x y hc => rationalPrimeTraceUnitH1_eq_of_evaluation_cups p hp q
      (σ.comp (rationalPrimeArithmeticRestriction a p hp))
      (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) hn x y
      (fun z => hc (rationalPrimeTraceIntegerH1Equiv p hp q
        (σ.comp (rationalPrimeArithmeticRestriction a p hp))
        (hσ.comp (rationalPrimeArithmeticRestriction a p hp).continuous) z))) u v h

end
end Dubon2026
