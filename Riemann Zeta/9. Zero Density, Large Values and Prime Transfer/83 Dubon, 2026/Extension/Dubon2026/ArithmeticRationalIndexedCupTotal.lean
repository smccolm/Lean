import Dubon2026.ArithmeticRationalIndexedRelationTotal
import Dubon2026.OriginalIndexedLocalCocycleInvariantFamily
import Dubon2026.OriginalAdicFiniteCupInvariant
import Dubon2026.RationalArithmeticOriginalCompletionRestriction
/-! Assemble the canonical rational total of the constructed indexed local cup family. This removes the supplied total and support comparisons from DUB-17's exceptional Cartier relation. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
attribute [-instance] UniformSpace.Completion.instSMul
  SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] originalAdicRelationCompletionAlgebra
  originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul indexedPrimeRelationCosets
  originalCompletionCarryValuation originalCompletionCarryLocalField
  finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul localRelationCupUnitsTopology
  localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

attribute [local instance] arithmeticOrbitLocalUnionAlgebra
  arithmeticOrbitCompletionNumberField rationalArithmeticOriginalFiniteGalois

variable (a : 𝓞 ℚ)
  (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (S : Finset (HeightOneSpectrum (𝓞 F)))
  (hS : ∀ (σ : Gal(F/ℚ)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv ℚ F σ v ∈ S)
  (I : Type) [Fintype I] (v : I → HeightOneSpectrum (𝓞 ℚ)) (w : I → S)
  [hLies : ∀ i, (w i).val.asIdeal.LiesOver (v i).asIdeal]
  (Ω : I → Type) [∀ i, Field (Ω i)]
  [∀ i, Algebra ((v i).adicCompletion ℚ) (Ω i)]
  [∀ i, Algebra ((w i).val.adicCompletion F) (Ω i)]
  [hTower : ∀ i, IsScalarTower ((v i).adicCompletion ℚ) ((w i).val.adicCompletion F) (Ω i)]
  [∀ i, IsGalois ((v i).adicCompletion ℚ) (Ω i)]
  [∀ i, IsSepClosed (Ω i)]
  (B : Rep.{0} ℤ Gal(F/ℚ)) [Finite B]


/-- One relation realizes the canonical rational total as the finite sum
of actual cup invariants on constructed continuous local H1 lifts. -/
theorem arithmeticRationalIndexedLocalCocycles_exists_cup_total
    (hv : Function.Injective v)
    (c : ∀ i : I, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom ℚ F (v i) (w i).val (Ω i) B)) :
    ∃ ψ : ∀ i : I,
      Rep.res (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits ((v i).adicCompletion ℚ) ((w i).val.adicCompletion F),
      (∀ (i : I) (z : galoisTowerLocalCoefficientH1
        ((v i).adicCompletion ℚ) ((w i).val.adicCompletion F) (Ω i) Gal(F/ℚ)
        (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B),
        galoisTowerLocalUnitCup ((v i).adicCompletion ℚ) ((w i).val.adicCompletion F)
          (Ω i) Gal(F/ℚ) (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B (c i) z =
        galoisTowerLocalUnitRelationConnecting ((v i).adicCompletion ℚ)
          ((w i).val.adicCompletion F) (Ω i) Gal(F/ℚ)
          (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B (ψ i) z) ∧
      ∀ y : groupCohomology B 1,
      ∃ x : ∀ i : I, galoisTowerFiniteLocalCoefficientH1 ((v i).adicCompletion ℚ)
        ((w i).val.adicCompletion F) Gal(F/ℚ)
        (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B,
      (∀ i : I, continuousH1ToAlgebraic
        (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B)
        continuous_of_discreteTopology (x i) =
        groupCohomology.map (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val)
          (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B)) 1 y) ∧
      arithmeticCommonStageRationalIdeleTotal a F
        ((groupCohomology.functor ℤ Gal(F/ℚ) 2).map (originalSPlaceFullIdeleInclusion ℚ F S hS)
          (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep ℚ F S hS)
            (originalIndexedPrimeSPlaceRelation ℚ F S hS I w B
              (fun j => originalAdicUnitRelationMorphism ℚ F (v j) (w j).val B (ψ j))) y)) =
        ∑ i : I, originalAdicFiniteLocalCupInvariant ℚ F (v i) (w i).val (Ω i) B (c i) (x i) := by
  have hrel := originalIndexedLocalCocycles_exists_SPlace_relation ℚ F S hS I v w Ω B hv
  with_reducible_and_instances
    have hr := hrel c
    unfold OriginalIndexedLocalCupFamilyRealization at hr
    obtain ⟨ψ, hψ, hc⟩ := hr
  refine ⟨ψ, hc, fun y => ?_⟩
  have h (i : I) := continuousH1ToAlgebraic_surjective
    (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B)
    continuous_of_discreteTopology
    (groupCohomology.map (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val)
      (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B)) 1 y)
  choose x hx using h
  refine ⟨x, hx, ?_⟩
  have hcup (i : I) :=
    (originalSPlaceRelation_completion_invariant ℚ F S hS (v i) (w i) (Ω i) B
      (originalIndexedPrimeSPlaceRelation ℚ F S hS I w B
        (fun j => originalAdicUnitRelationMorphism ℚ F (v j) (w j).val B (ψ j)))
      (ψ i) (hψ i) y (x i) (hx i)).trans
      (congrArg (localFieldContinuousH2InvariantEquiv ((v i).adicCompletion ℚ) (Ω i))
        (hc i (galoisTowerFiniteLocalH1Inflation ((v i).adicCompletion ℚ)
          ((w i).val.adicCompletion F) (Ω i) Gal(F/ℚ)
          (originalAdicCompletionGaloisInclusion ℚ F (v i) (w i).val) B (x i))).symm)
  have hsum := arithmeticRationalIndexedRelation_total_eq_sum a F S hS I v w B hv
    (fun i => originalFinitePrimeBelow_eq_of_liesOver ℚ F (v i) (w i).val)
    (fun j => originalAdicUnitRelationMorphism ℚ F (v j) (w j).val B (ψ j)) y
  have hreal : OriginalPrimeInvariantRealization ℚ F
      (arithmeticCommonStageRationalPrimeInvariant a F) :=
    arithmeticCommonStageRationalPrimeInvariant_realization a F
  unfold OriginalPrimeInvariantRealization at hreal
  have hrealAt (i : I) := @hreal (v i) (w i).val (hLies i) (Ω i) _ _ _ (hTower i) _ _ _ _
  have hpoint (i : I) := (hrealAt i _).trans (hcup i)
  with_reducible_and_instances
    refine hsum.trans (Finset.sum_congr rfl (fun i _ => ?_))
    unfold originalAdicFiniteLocalCupInvariant
    exact hpoint i

end
end Dubon2026
