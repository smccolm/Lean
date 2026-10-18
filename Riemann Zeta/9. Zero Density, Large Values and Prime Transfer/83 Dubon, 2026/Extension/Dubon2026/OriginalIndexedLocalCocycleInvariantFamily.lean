import Dubon2026.OriginalIndexedLocalCocycleRelationFamily
import Dubon2026.OriginalSPlaceLocalRelationInvariant
import Dubon2026.ContinuousDiscreteH1Surjection

/-! Construct the finite S-place relation from the actual local Hom cocycles.
Each local cup representative is constructed by Hilbert 90 and same-field
descent; native coinduction then recovers all its literal local values. This
consumes the local construction rather than asking for relation morphisms. -/

namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2 Submodule.module Submodule.Quotient.module
attribute [local instance] originalAdicRelationCompletionAlgebra
  originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul indexedPrimeRelationCosets
  originalCompletionCarryValuation originalCompletionCarryLocalField
  finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul localRelationCupUnitsTopology
  localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (I : Type) [Fintype I] (v : I → HeightOneSpectrum (𝓞 K)) (w : I → S)
  [∀ i, (w i).val.asIdeal.LiesOver (v i).asIdeal]
  (Ω : I → Type) [∀ i, Field (Ω i)]
  [∀ i, Algebra ((v i).adicCompletion K) (Ω i)]
  [∀ i, Algebra ((w i).val.adicCompletion L) (Ω i)]
  [∀ i, IsScalarTower ((v i).adicCompletion K) ((w i).val.adicCompletion L) (Ω i)]
  [∀ i, IsGalois ((v i).adicCompletion K) (Ω i)]
  [∀ i, IsSepClosed (Ω i)]
  (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- Exact completion-invariant realization by one indexed relation and actual
continuous lifts of every restricted global H1 class. This is a statement,
not an assumed completion-invariant identity. -/
def OriginalIndexedLocalCupInvariantRealization
    (c : ∀ i : I, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L (v i) (w i).val (Ω i) B)) : Prop :=
    ∃ ψ : ∀ i : I,
      Rep.res (originalAdicCompletionGaloisInclusion K L (v i) (w i).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits ((v i).adicCompletion K) ((w i).val.adicCompletion L),
      ∀ y : groupCohomology B 1,
      ∃ x : ∀ i : I, galoisTowerFiniteLocalCoefficientH1 ((v i).adicCompletion K)
        ((w i).val.adicCompletion L) Gal(L/K)
        (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B,
      (∀ i : I, continuousH1ToAlgebraic
        (Rep.res (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B)
        continuous_of_discreteTopology (x i) =
        groupCohomology.map (originalAdicCompletionGaloisInclusion K L (v i) (w i).val)
          (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B)) 1 y) ∧
      ∀ i : I,
        originalFullIdeleCompletionInvariant K L (v i) (w i).val (Ω i)
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
            (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
              (originalIndexedPrimeSPlaceRelation K L S hS I w B
                (fun j => originalAdicUnitRelationMorphism K L (v j) (w j).val B (ψ j))) y)) =
        localFieldContinuousH2InvariantEquiv ((v i).adicCompletion K) (Ω i)
          (galoisTowerLocalUnitCup ((v i).adicCompletion K) ((w i).val.adicCompletion L) (Ω i)
            Gal(L/K) (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B (c i)
            (galoisTowerFiniteLocalH1Inflation ((v i).adicCompletion K) ((w i).val.adicCompletion L)
              (Ω i) Gal(L/K) (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B (x i)))

/-- The actual cocycle family constructs its relation and every finite
continuous H1 lift, and proves all normalized completion invariants. -/
theorem originalIndexedLocalCocycles_exists_completion_invariants
    (hv : Function.Injective v)
    (c : ∀ i : I, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L (v i) (w i).val (Ω i) B)) :
    OriginalIndexedLocalCupInvariantRealization K L S hS I v w Ω B c := by
  unfold OriginalIndexedLocalCupInvariantRealization
  have hsource := originalIndexedLocalCocycles_exists_SPlace_relation K L S hS I v w Ω B hv c
  obtain ⟨ψ, hψ, hc⟩ := hsource
  refine ⟨ψ, fun y => ?_⟩
  have h (i : I) := continuousH1ToAlgebraic_surjective
    (Rep.res (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B)
    continuous_of_discreteTopology
    (groupCohomology.map (originalAdicCompletionGaloisInclusion K L (v i) (w i).val)
      (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B)) 1 y)
  choose x hx using h
  refine ⟨x, hx, fun i => ?_⟩
  let Φ := originalIndexedPrimeSPlaceRelation K L S hS I w B
    (fun j => originalAdicUnitRelationMorphism K L (v j) (w j).val B (ψ j))
  exact (originalSPlaceRelation_completion_invariant K L S hS (v i) (w i) (Ω i) B
    Φ (ψ i) (hψ i) y (x i) (hx i)).trans
    (congrArg (localFieldContinuousH2InvariantEquiv ((v i).adicCompletion K) (Ω i))
      (hc i (galoisTowerFiniteLocalH1Inflation ((v i).adicCompletion K) ((w i).val.adicCompletion L)
        (Ω i) Gal(L/K) (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B (x i))).symm)

end
end Dubon2026
