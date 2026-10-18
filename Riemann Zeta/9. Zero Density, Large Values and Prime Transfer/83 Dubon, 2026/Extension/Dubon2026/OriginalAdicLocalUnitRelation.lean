import Dubon2026.GaloisTowerLocalUnitRelation
import Dubon2026.OriginalAdicUnitRelationTransport

/-! Actual local relation representatives at the original number-field
completion. The free cover, relation kernel, decomposition action and unit
values are the literal source objects. Native finite Galois completion and
the proved Hilbert-90 lift supply the hypotheses, serving DUB-17's local
family realization before the required cup-total comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra
variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The literal completion extension has the proved original Galois structure. -/
local instance originalAdicLocalRelationGalois :
    IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  (originalAdicBaseChange_finite_galois K L v w).2

variable (Ω : Type) [Field Ω] [Algebra (v.adicCompletion K) Ω]
  [Algebra (w.adicCompletion L) Ω] [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] (B : Rep.{0} ℤ Gal(L/K))

/-- The original local Hom coefficient with the actual completion-to-global group map. -/
abbrev originalAdicLocalCoefficientUnitHom :=
  galoisTowerLocalCoefficientUnitHom (v.adicCompletion K) (w.adicCompletion L) Ω
    Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B

variable [TopologicalSpace (originalAdicLocalCoefficientUnitHom K L v w Ω B)]
  [DiscreteTopology (originalAdicLocalCoefficientUnitHom K L v w Ω B)]

/-- Integer multiplication is continuous on the original discrete local coefficient Hom. -/
local instance originalAdicLocalCoefficientHomContinuousSMul :
    @ContinuousSMul ℤ (originalAdicLocalCoefficientUnitHom K L v w Ω B)
      (originalAdicLocalCoefficientUnitHom K L v w Ω B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (originalAdicLocalCoefficientUnitHom K L v w Ω B)
    (originalAdicLocalCoefficientUnitHom K L v w Ω B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- Every original continuous local Hom cocycle has a relation representative
in the literal completion units with their original decomposition action.
The displayed lift identity retains the data needed for the local cup square. -/
theorem originalAdicLocalUnitCocycle_exists_relation_representative
    (c : continuousRepresentationCocyclesOne (originalAdicLocalCoefficientUnitHom K L v w Ω B)) :
    let ι := originalAdicCompletionGaloisInclusion K L v w
    let π : Gal(Ω/v.adicCompletion K) →* Gal(L/K) := ι.comp (AlgEquiv.restrictNormalHom (w.adicCompletion L))
    let X := (originalRelationShortComplex B).map (Rep.resFunctor π)
    let C := Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω
    ∃ u : galoisTowerPartialFreeUnitHom (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) ι B,
      ∃ φ : Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
        originalAdicUnitRep K L w,
        (∀ x : originalRelationModule B,
          (finiteGaloisUnitTowerInclusion (v.adicCompletion K) (w.adicCompletion L) Ω).hom
            (show Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L) from φ.hom x) =
              DFunLike.coe (F := X.X₂ →ₗ[ℤ] C) u (X.f.hom x)) ∧
        ∀ g, (galoisTowerPartialFreeUnitHom (v.adicCompletion K) (w.adicCompletion L) Ω
          Gal(L/K) ι B).ρ g u - u = (originalInternalHomPrecomposition C X.g).hom (c.val g) := by
  obtain ⟨u, ψ, he, hu⟩ := galoisTowerLocalUnitCocycle_exists_relation_representative
    (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K)
    (originalAdicCompletionGaloisInclusion K L v w) B
    (originalAdicCompletionGaloisInclusion_injective K L v w) c
  refine ⟨u, originalAdicUnitRelationMorphism K L v w B ψ, ?_, hu⟩
  intro x
  exact LinearMap.congr_fun he x

end
end Dubon2026
