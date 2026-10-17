import Dubon2026.ArithmeticRelationClassHomDescent
import Dubon2026.OriginalRelationGroupChange

/-! # Actual finite relation morphism from the arithmetic class colimit

Surjective Galois restriction descends the original lattice morphism.
Precomposition with the canonical relation-presentation map gives a
morphism from the relation module at that very same finite stage. This
is the literal input to the proved finite relation criterion on DUB-17's
degree-one class/Ext and reverse-localization dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B]

/-- An actual arithmetic relation-to-class morphism yields a genuine
finite-stage relation morphism, with exactly the canonical relation
restriction and the original class-colimit inclusion in its value formula. -/
theorem arithmeticRelationClassHom_exists_finite_relation_descent
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K))
        (originalRelationModule B) ⟶ arithmeticClassesModOutsideColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hPN : P ≤ N,
        letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
        let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
        ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticClassesModOutsideStageRep K Ω a ha N,
          ∀ r, (coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N).hom (η.hom r) =
              φ.hom ((originalRelationGroupChange τ B).hom r) := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨N, hPN, ψ, hψ⟩ := arithmeticRelationClassHom_exists_stage K Ω a ha P B φ
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    .of_algebraMap_eq' rfl
  letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(N/K) :=
    AlgEquiv.restrictNormalHom N
  let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
  let RN := Rep.res τ (originalRelationModule B)
  let C := arithmeticClassesModOutsideStageRep K Ω a ha N
  let χ : Rep.res π RN ⟶ Rep.res π C := Rep.ofHom {
    toLinearMap := ψ.hom.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro r
      change ψ.hom ((originalRelationModule B).ρ
        (AlgEquiv.restrictNormalHom P (AlgEquiv.restrictNormalHom N g)) r) =
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha N).ρ g (ψ.hom r)
      rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply P N g]
      exact Rep.hom_comm_apply ψ g r }
  have hπ : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective _
  let β := Rep.liftHomOfSurj π hπ χ
  let η := originalRelationGroupChange τ B ≫ β
  refine ⟨N, hPN, η, ?_⟩
  intro r
  exact congrArg (fun m => m.hom ((originalRelationGroupChange τ B).hom r)) hψ

end
end Dubon2026
