import Dubon2026.OriginalFiniteLocalCocycleRelationFamily
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
  originalAdicRelationCupHomContinuousSMul finitePrimeRelationCosets finiteLocalRelationFamilyLiesOver
  originalCompletionCarryValuation originalCompletionCarryLocalField
  finiteLocalRelationCoefficientTopology finiteLocalRelationCoefficientDiscrete
  finiteLocalRelationCoefficientContinuousSMul localRelationCupUnitsTopology
  localRelationCupUnitsDiscrete localRelationCupUnitsContinuousSMul

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 K))) (w : T → S)
  [hw : Fact (∀ v : T, originalFinitePrimeBelow K L (w v).val = v.val)]

variable (Ω : T → Type) [∀ v, Field (Ω v)]
  [∀ v, Algebra (v.val.adicCompletion K) (Ω v)]
  [∀ v, Algebra ((w v).val.adicCompletion L) (Ω v)]
  [∀ v, IsScalarTower (v.val.adicCompletion K) ((w v).val.adicCompletion L) (Ω v)]
  [∀ v, IsGalois (v.val.adicCompletion K) (Ω v)] [∀ v, IsSepClosed (Ω v)]
  (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- The actual local Hom-cocycle family constructs one S-place relation
whose normalized full-idele completion invariant is the invariant of the
original local cup on an actual lift of each restricted global H1 class. -/
theorem originalFiniteLocalCocycles_exists_completion_invariants
    (c : ∀ v : T, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L v.val (w v).val (Ω v) B)) :
    ∃ ψ : ∀ v : T,
      Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits (v.val.adicCompletion K) ((w v).val.adicCompletion L),
      ∀ y : groupCohomology B 1,
      ∃ x : ∀ v : T, galoisTowerFiniteLocalCoefficientH1 (v.val.adicCompletion K)
        ((w v).val.adicCompletion L) Gal(L/K)
        (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B,
      (∀ v : T, continuousH1ToAlgebraic
        (Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B)
        continuous_of_discreteTopology (x v) =
        groupCohomology.map (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
          (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B)) 1 y) ∧
      ∀ v : T,
        originalFullIdeleCompletionInvariant K L v.val (w v).val (Ω v)
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
            (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
              (originalFinitePrimeSPlaceRelation K L S hS T w B
                (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))) y)) =
        localFieldContinuousH2InvariantEquiv (v.val.adicCompletion K) (Ω v)
          (galoisTowerLocalUnitCup (v.val.adicCompletion K) ((w v).val.adicCompletion L) (Ω v)
            Gal(L/K) (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (c v)
            (galoisTowerFiniteLocalH1Inflation (v.val.adicCompletion K) ((w v).val.adicCompletion L)
              (Ω v) Gal(L/K) (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (x v))) := by
  have hsource := originalFiniteLocalCocycles_exists_SPlace_relation K L S hS T w Ω B c
  obtain ⟨ψ, hψ, hc⟩ := hsource
  refine ⟨ψ, fun y => ?_⟩
  have h (v : T) := continuousH1ToAlgebraic_surjective
    (Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B)
    continuous_of_discreteTopology
    (groupCohomology.map (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
      (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B)) 1 y)
  choose x hx using h
  refine ⟨x, hx, fun v => ?_⟩
  let Φ := originalFinitePrimeSPlaceRelation K L S hS T w B
    (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))
  exact (originalSPlaceRelation_completion_invariant K L S hS v.val (w v) (Ω v) B
    Φ (ψ v) (hψ v) y (x v) (hx v)).trans
    (congrArg (localFieldContinuousH2InvariantEquiv (v.val.adicCompletion K) (Ω v))
      (hc v (galoisTowerFiniteLocalH1Inflation (v.val.adicCompletion K) ((w v).val.adicCompletion L)
        (Ω v) Gal(L/K) (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (x v))).symm)

end
end Dubon2026
