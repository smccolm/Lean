import Dubon2026.OriginalAdicUnitCohomology
import Dubon2026.OriginalRelationModuleSequence

/-! Retain the original completion units and original decomposition action
in DUB-17's local relation morphism. The native completion Galois equivalence
removes a group-identification premise before coinduction. -/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- Use the literal original completion embedding for its Galois action. -/
local instance originalAdicRelationCompletionAlgebra :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (originalAdicBaseChangeMap K L v w).toAlgebra

/-- The actual local completion automorphism is its original global
decomposition-group element, included in the original global Galois group. -/
def originalAdicCompletionGaloisInclusion : Gal(w.adicCompletion L/v.adicCompletion K) →* Gal(L/K) :=
  (OriginalFiniteDecompositionGroup K L w).subtype.comp
    (originalAdicDecompositionGaloisEquiv K L v w).symm.toMonoidHom

/-- The actual local-to-global finite group inclusion is injective, with
no full-decomposition assumption. -/
theorem originalAdicCompletionGaloisInclusion_injective :
    Function.Injective (originalAdicCompletionGaloisInclusion K L v w) :=
  (Subgroup.subtype_injective _).comp (originalAdicDecompositionGaloisEquiv K L v w).symm.injective

variable (B : Rep.{0} ℤ Gal(L/K))

/-- The original local Galois relation morphism gives the same literal
completion-unit values with the original decomposition-group action. -/
def originalAdicUnitRelationMorphism
    (ψ : Rep.res (originalAdicCompletionGaloisInclusion K L v w) (originalRelationModule B) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) :
    Rep.res (OriginalFiniteDecompositionGroup K L w).subtype (originalRelationModule B) ⟶
      originalAdicUnitRep K L w :=
  Rep.ofHom {
    toLinearMap := (originalAdicUnitCoefficientIso K L v w).hom.hom.toLinearMap.comp
      ψ.hom.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      have hψ := Rep.hom_comm_apply ψ (originalAdicDecompositionGaloisEquiv K L v w g) x
      have hi := Rep.hom_comm_apply (originalAdicUnitCoefficientIso K L v w).hom g (ψ.hom x)
      have he : originalAdicCompletionGaloisInclusion K L v w
          (originalAdicDecompositionGaloisEquiv K L v w g) = g.val :=
        congrArg Subtype.val ((originalAdicDecompositionGaloisEquiv K L v w).symm_apply_apply g)
      change ψ.hom ((originalRelationModule B).ρ
        (originalAdicCompletionGaloisInclusion K L v w (originalAdicDecompositionGaloisEquiv K L v w g)) x) = _ at hψ
      rw [he] at hψ
      exact (congrArg (originalAdicUnitCoefficientIso K L v w).hom.hom hψ).trans hi }

/-- Transport keeps each actual original completion unit unchanged. -/
theorem originalAdicUnitRelationMorphism_apply
    (ψ : Rep.res (originalAdicCompletionGaloisInclusion K L v w) (originalRelationModule B) ⟶
      Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (x : originalRelationModule B) :
    (originalAdicUnitRelationMorphism K L v w B ψ).hom x = ψ.hom x := rfl

end
end Dubon2026
