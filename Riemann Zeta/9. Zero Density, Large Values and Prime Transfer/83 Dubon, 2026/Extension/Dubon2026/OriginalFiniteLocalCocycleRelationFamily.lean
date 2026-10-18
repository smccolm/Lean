import Dubon2026.OriginalAdicLocalUnitRelationCup
import Dubon2026.OriginalFinitePrimeRelationConnecting

/-! Construct the finite S-place relation from the actual local Hom cocycles.
Each local cup representative is constructed by Hilbert 90 and same-field
descent; native coinduction then recovers all its literal local values. This
consumes the local construction rather than asking for relation morphisms. -/

namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra
  originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul finitePrimeRelationCosets

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
  (T : Finset (HeightOneSpectrum (𝓞 K))) (w : T → S)
  [hw : Fact (∀ v : T, originalFinitePrimeBelow K L (w v).val = v.val)]

/-- The specified prime contraction derives the actual lying-over relation. -/
local instance finiteLocalRelationFamilyLiesOver (v : T) :
    (w v).val.asIdeal.LiesOver v.val.asIdeal := by
  rw [← hw.out v]
  exact originalFinitePrimeBelow_liesOver K L (w v).val

variable (Ω : T → Type) [∀ v, Field (Ω v)]
  [∀ v, Algebra (v.val.adicCompletion K) (Ω v)]
  [∀ v, Algebra ((w v).val.adicCompletion L) (Ω v)]
  [∀ v, IsScalarTower (v.val.adicCompletion K) ((w v).val.adicCompletion L) (Ω v)]
  [∀ v, IsGalois (v.val.adicCompletion K) (Ω v)]
  (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- The actual finite local Hom-cocycle family constructs one S-place relation
with exactly the original local values and with all its local cup identities.
Completion Galois structure, free lifts, descent and orbit separation are derived. -/
theorem originalFiniteLocalCocycles_exists_SPlace_relation
    (c : ∀ v : T, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L v.val (w v).val (Ω v) B)) :
    ∃ ψ : ∀ v : T,
      Rep.res (originalAdicCompletionGaloisInclusion K L v.val (w v).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits (v.val.adicCompletion K) ((w v).val.adicCompletion L),
      (∀ (v : T) (x : originalRelationModule B),
        (originalFinitePrimeSPlaceRelation K L S hS T w B
          (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u))).hom
          x (Sum.inr (w v)) = (ψ v).hom x) ∧
      ∀ (v : T) (x : galoisTowerLocalCoefficientH1
        (v.val.adicCompletion K) ((w v).val.adicCompletion L) (Ω v) Gal(L/K)
        (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B),
        galoisTowerLocalUnitCup (v.val.adicCompletion K) ((w v).val.adicCompletion L)
          (Ω v) Gal(L/K) (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (c v) x =
        galoisTowerLocalUnitRelationConnecting (v.val.adicCompletion K)
          ((w v).val.adicCompletion L) (Ω v) Gal(L/K)
          (originalAdicCompletionGaloisInclusion K L v.val (w v).val) B (ψ v) x := by
  have h (v : T) := originalAdicLocalUnitCocycle_exists_relation_cup
    K L v.val (w v).val (Ω v) B (c v)
  choose ψ hψ using h
  refine ⟨ψ, ?_, hψ⟩
  intro v x
  exact (originalFinitePrimeSPlaceRelation_evaluation K L S hS T w B hw.out
    (fun u => originalAdicUnitRelationMorphism K L u.val (w u).val B (ψ u)) v x).trans
    (originalAdicUnitRelationMorphism_apply K L v.val (w v).val B (ψ v) x)

end
end Dubon2026
