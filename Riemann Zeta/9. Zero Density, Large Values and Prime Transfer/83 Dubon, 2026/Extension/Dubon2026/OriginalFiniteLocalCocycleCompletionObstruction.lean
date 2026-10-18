import Dubon2026.OriginalFiniteLocalCocycleRelationFamily
import Dubon2026.OriginalSPlaceRelationCompletionObstruction

/-! Construct the finite S-place relation from the actual local Hom cocycles.
Each local relation is constructed. The literal full-idele completion map
identifies its original finite obstruction with the local connecting class,
while the same witness retains every continuous local cup identity. -/

namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra
  originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul finitePrimeRelationCosets finiteLocalRelationFamilyLiesOver

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
  [∀ v, IsGalois (v.val.adicCompletion K) (Ω v)]
  (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- The actual finite local Hom-cocycle family constructs one S-place relation
with exactly the original finite completion obstructions and all local cup
identities. The required coefficient comparisons and local relations are derived. -/
theorem originalFiniteLocalCocycles_exists_completion_obstruction
    (c : ∀ v : T, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L v.val (w v).val (Ω v) B)) :
    ∃ ψ : ∀ v : T,
      Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits (v.val.adicCompletion K) ((w v).val.adicCompletion L),
      (∀ (v : T) (y : groupCohomology B 1),
        originalFullIdeleCompletionH2 K L v.val (w v).val
          ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSPlaceFullIdeleInclusion K L S hS)
            (originalRelationExtensionObstruction B (supportedUnrestrictedUnitRep K L S hS)
              (originalFinitePrimeSPlaceRelation K L S hS T w B
                (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))) y)) =
        (groupCohomology.functor ℤ Gal((w v).val.adicCompletion L/v.val.adicCompletion K) 2).map (ψ v)
          (groupCohomology.δ (originalRelationGroupChange_shortExact
            (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B) 1 2 rfl
            (groupCohomology.map (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
              (𝟙 (Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B)) 1 y))) ∧
      ∀ (v : T) (x : galoisTowerLocalCoefficientH1
        (v.val.adicCompletion K) ((w v).val.adicCompletion L) (Ω v) Gal(L/K)
        (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B),
        galoisTowerLocalUnitCup (v.val.adicCompletion K) ((w v).val.adicCompletion L)
          (Ω v) Gal(L/K) (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (c v) x =
        galoisTowerLocalUnitRelationConnecting (v.val.adicCompletion K)
          ((w v).val.adicCompletion L) (Ω v) Gal(L/K)
          (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (ψ v) x := by
  obtain ⟨ψ, hψ, hc⟩ := originalFiniteLocalCocycles_exists_SPlace_relation K L S hS T w Ω B c
  refine ⟨ψ, ?_, hc⟩
  intro v y
  exact originalSPlaceRelation_completion_obstruction K L S hS v.val (w v) B
    (originalFinitePrimeSPlaceRelation K L S hS T w B
      (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u)))
    (ψ v) (hψ v) y

end
end Dubon2026
