import Dubon2026.GaloisTowerLocalUnitRelationCup
import Dubon2026.OriginalAdicLocalUnitRelation

/-! The original local completion relation morphism represents all its
continuous unit cups. The native finite Galois completion and actual
decomposition inclusion discharge the group hypotheses. This is DUB-17's
local relation/cup square before invariant and S-place sum comparison. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV2
attribute [local instance] originalAdicRelationCompletionAlgebra originalAdicLocalRelationGalois
variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The original completion extension has its proved finite dimension. -/
local instance originalAdicLocalRelationCupFinite :
    FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
  (originalAdicBaseChange_finite_galois K L v w).1

variable (Ω : Type) [Field Ω] [Algebra (v.adicCompletion K) Ω]
  [Algebra (w.adicCompletion L) Ω] [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] (B : Rep.{0} ℤ Gal(L/K)) [Finite B]

/-- Use the original discrete local Hom topology. -/
local instance originalAdicRelationCupHomTopology :
    TopologicalSpace (originalAdicLocalCoefficientUnitHom K L v w Ω B) := ⊥
/-- The original local Hom coefficient is discrete. -/
local instance originalAdicRelationCupHomDiscrete :
    DiscreteTopology (originalAdicLocalCoefficientUnitHom K L v w Ω B) := ⟨rfl⟩
/-- Integer scalars act continuously on the original discrete local Hom. -/
local instance originalAdicRelationCupHomContinuousSMul :
    @ContinuousSMul ℤ (originalAdicLocalCoefficientUnitHom K L v w Ω B)
      (originalAdicLocalCoefficientUnitHom K L v w Ω B).hV2.toSMul inferInstance inferInstance :=
  @ContinuousSMul.mk ℤ (originalAdicLocalCoefficientUnitHom K L v w Ω B)
    (originalAdicLocalCoefficientUnitHom K L v w Ω B).hV2.toSMul _ _ continuous_of_discreteTopology

/-- One original completion-unit relation morphism represents every
continuous cup with the given actual local Hom cocycle. No completion
Galois, full-decomposition, lifting or continuity hypothesis is supplied. -/
theorem originalAdicLocalUnitCocycle_exists_relation_cup
    (c : continuousRepresentationCocyclesOne (originalAdicLocalCoefficientUnitHom K L v w Ω B)) :
    let ι := originalAdicCompletionGaloisInclusion K L v w
    ∃ ψ : Rep.res ι (originalRelationModule B) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L),
      ∀ x : galoisTowerLocalCoefficientH1 (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) ι B,
        galoisTowerLocalUnitCup (v.adicCompletion K) (w.adicCompletion L) Ω Gal(L/K) ι B c x =
          galoisTowerLocalUnitRelationConnecting (v.adicCompletion K) (w.adicCompletion L) Ω
            Gal(L/K) ι B ψ x :=
  galoisTowerLocalUnitCocycle_exists_relation_cup (v.adicCompletion K) (w.adicCompletion L) Ω
    Gal(L/K) (originalAdicCompletionGaloisInclusion K L v w) B
    (originalAdicCompletionGaloisInclusion_injective K L v w) c

end
end Dubon2026
