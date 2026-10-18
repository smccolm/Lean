import Dubon2026.OriginalFiniteLocalCocycleInvariantFamily
import Dubon2026.OriginalAdicFiniteCupInvariant
import Dubon2026.OriginalSPlaceLocalRelationInvariant
import Dubon2026.ContinuousDiscreteH1Surjection

/-! Construct the finite S-place relation from the actual local Hom cocycles.
Each local cup representative is constructed by Hilbert 90 and same-field
descent; native coinduction then recovers all its literal local values. This
consumes the local construction rather than asking for relation morphisms. -/

namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
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

/-- A total whose values on the original finite relations are identified
with their completion sums gives the cup total for the constructed family.
The actual arithmetic consumer proves this comparison for its canonical total. -/
theorem originalFiniteLocalCocycles_exists_cup_total
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (htotal : ∀ (ψ : ∀ v : T,
      Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits (v.val.adicCompletion K) ((w v).val.adicCompletion L))
      (y : groupCohomology B 1),
      total ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
          (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
            (originalFinitePrimeSPlaceRelation K L S hS T w B
              (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))) y)) = ∑ v : T,
        originalFullIdeleCompletionInvariant K L v.val (w v).val (Ω v) ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
          (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
            (originalFinitePrimeSPlaceRelation K L S hS T w B
              (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))) y)))
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
      total ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
          (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
            (originalFinitePrimeSPlaceRelation K L S hS T w B
              (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))) y)) = ∑ v : T,
        originalAdicFiniteLocalCupInvariant K L v.val (w v).val (Ω v) B (c v) (x v) := by
  have hsource := originalFiniteLocalCocycles_exists_completion_invariants K L S hS T w Ω B c
  refine Exists.imp (fun ψ hψ y => ?_) hsource
  refine Exists.imp (fun x hx => ?_) (hψ y)
  exact ⟨hx.1, (htotal ψ y).trans (Finset.sum_congr rfl (fun v _ => hx.2 v))⟩

end
end Dubon2026
