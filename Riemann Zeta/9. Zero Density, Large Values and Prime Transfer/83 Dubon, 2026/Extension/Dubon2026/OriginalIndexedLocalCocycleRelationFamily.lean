import Dubon2026.OriginalIndexedPrimeSPlaceRelation
import Dubon2026.OriginalAdicLocalUnitRelationCup
import Dubon2026.OriginalFullIdeleInvariantPrimeSupport

/-! Assemble the actual finitely indexed original local Hom cocycles.
This is used for the original exceptional rational-prime Cartier family
in DUB-17: the literal prime indices, completion fields and cocycles stay
unchanged, while native Hilbert 90/descent and single-prime coinduction
construct their common S-place relation. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV1 Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra
  originalAdicLocalRelationGalois originalAdicLocalRelationCupFinite
  originalAdicRelationCupHomTopology originalAdicRelationCupHomDiscrete
  originalAdicRelationCupHomContinuousSMul indexedPrimeRelationCosets

variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) u, u ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ u ∈ S)
  (I : Type) [Fintype I] (v : I → HeightOneSpectrum (𝓞 K)) (w : I → S)
  [∀ i, (w i).val.asIdeal.LiesOver (v i).asIdeal]
  (Ω : I → Type) [∀ i, Field (Ω i)]
  [∀ i, Algebra ((v i).adicCompletion K) (Ω i)]
  [∀ i, Algebra ((w i).val.adicCompletion L) (Ω i)]
  [∀ i, IsScalarTower ((v i).adicCompletion K) ((w i).val.adicCompletion L) (Ω i)]
  [∀ i, IsGalois ((v i).adicCompletion K) (Ω i)]
  (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- The actual indexed S-place sum recovers all specified local relation
values and represents all local cups. This predicate states the conclusion;
it supplies no mathematical assumption or proof by itself. -/
def OriginalIndexedLocalCupFamilyRealization
    (c : ∀ i : I, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L (v i) (w i).val (Ω i) B)) : Prop :=
    ∃ ψ : ∀ i : I,
      Rep.res (originalAdicCompletionGaloisInclusion K L (v i) (w i).val)
        (originalRelationModule B) ⟶
        Rep.ofAlgebraAutOnUnits ((v i).adicCompletion K) ((w i).val.adicCompletion L),
      (∀ (i : I) (x : originalRelationModule B),
        (originalIndexedPrimeSPlaceRelation K L S hS I w B
          (fun j => originalAdicUnitRelationMorphism K L (v j) (w j).val B (ψ j))).hom
          x (Sum.inr (w i)) = (ψ i).hom x) ∧
      ∀ (i : I) (x : galoisTowerLocalCoefficientH1
        ((v i).adicCompletion K) ((w i).val.adicCompletion L) (Ω i) Gal(L/K)
        (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B),
        galoisTowerLocalUnitCup ((v i).adicCompletion K) ((w i).val.adicCompletion L)
          (Ω i) Gal(L/K) (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B (c i) x =
        galoisTowerLocalUnitRelationConnecting ((v i).adicCompletion K)
          ((w i).val.adicCompletion L) (Ω i) Gal(L/K)
          (originalAdicCompletionGaloisInclusion K L (v i) (w i).val) B (ψ i) x

/-- Native local relation construction and coinduction realize the entire
original indexed cocycle family, with every local value and cup identity. -/
theorem originalIndexedLocalCocycles_exists_SPlace_relation
    (hv : Function.Injective v)
    (c : ∀ i : I, continuousRepresentationCocyclesOne
      (originalAdicLocalCoefficientUnitHom K L (v i) (w i).val (Ω i) B)) :
    OriginalIndexedLocalCupFamilyRealization K L S hS I v w Ω B c := by
  unfold OriginalIndexedLocalCupFamilyRealization
  have h (i : I) := originalAdicLocalUnitCocycle_exists_relation_cup
    K L (v i) (w i).val (Ω i) B (c i)
  choose ψ hψ using h
  have hw : Function.Injective (fun i : I => originalFinitePrimeBelow K L (w i).val) := by
    intro i j hij
    apply hv
    rw [← originalFinitePrimeBelow_eq_of_liesOver K L (v i) (w i).val,
      ← originalFinitePrimeBelow_eq_of_liesOver K L (v j) (w j).val]
    exact hij
  refine ⟨ψ, ?_, hψ⟩
  intro i x
  exact (originalIndexedPrimeSPlaceRelation_evaluation K L S hS I w B hw
    (fun j => originalAdicUnitRelationMorphism K L (v j) (w j).val B (ψ j)) i x).trans
    (originalAdicUnitRelationMorphism_apply K L (v i) (w i).val B (ψ i) x)

end
end Dubon2026
