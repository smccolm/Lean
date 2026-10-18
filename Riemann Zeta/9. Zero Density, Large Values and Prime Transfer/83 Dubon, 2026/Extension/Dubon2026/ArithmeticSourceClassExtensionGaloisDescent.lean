import Dubon2026.ArithmeticSourceClassExtensionDescent
import Dubon2026.OriginalRelationGroupChange

/-! Turn the descended source-class extension into a morphism for the
actual finite Galois group. The canonical map of free presentations
retains its exact relation equation. This supplies the projective finite
cover needed for DUB-17's S-unit correction, with no extra equivariance
or relation-compatibility assumption. -/
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

/-- A colimit source-class extension of the actual relation produces a
finite Galois-stage extension of its canonical changed presentation. -/
theorem arithmeticSourceClassExtension_exists_finite_galois_extension :
    let πP : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K) :=
      AlgEquiv.restrictNormalHom P
    ∀ (φ : originalRelationModule B ⟶ ArithmeticSPlaceClassFiniteStageRep K Ω a ha P)
      (f : Rep.res πP (Rep.free ℤ Gal(P/K) B) ⟶ arithmeticSPlaceClassColimitRep K Ω a ha),
      (Rep.resFunctor πP).map (originalRelationInclusion B) ≫ f =
        (Rep.resFunctor πP).map φ ≫ coefficientRepresentationColimitOf _
          (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P →
      ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
          letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
          let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
          ∃ fN : Rep.free ℤ Gal(N/K) (Rep.res τ B) ⟶ ArithmeticSPlaceClassFiniteStageRep K Ω a ha N,
            originalRelationInclusion (Rep.res τ B) ≫ fN =
              originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map φ ≫
                arithmeticSPlaceClassFiniteTransition K Ω a ha P N hPN := by
  intro πP φ f hf
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  have hdescent := arithmeticSourceClassExtension_exists_stage_with_relation K Ω a ha P B
  dsimp only [originalRelationShortComplex, ShortComplex.map, Rep.resFunctor,
    arithmeticGlobalSPlaceClassStageRep, restrictedCoefficientRep] at hdescent
  obtain ⟨N, hPN, ψ, _, hrel⟩ := hdescent ((Rep.resFunctor πP).map φ) f hf
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    .of_algebraMap_eq' rfl
  letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(N/K) :=
    AlgEquiv.restrictNormalHom N
  let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
  let PN := Rep.res τ (Rep.free ℤ Gal(P/K) B)
  let C := ArithmeticSPlaceClassFiniteStageRep K Ω a ha N
  let χ : Rep.res π PN ⟶ Rep.res π C := Rep.ofHom {
    toLinearMap := ψ.hom.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      change ψ.hom ((Rep.free ℤ Gal(P/K) B).ρ
        (AlgEquiv.restrictNormalHom P (AlgEquiv.restrictNormalHom N g)) x) =
          (arithmeticGlobalSPlaceClassStageRep K Ω a ha N).ρ g (ψ.hom x)
      have hcomp := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply P N g
      exact (congrArg (fun t : Gal(P/K) => ψ.hom ((Rep.free ℤ Gal(P/K) B).ρ t x))
        hcomp.symm).trans (Rep.hom_comm_apply ψ g x) }
  let β := Rep.liftHomOfSurj π (AlgEquiv.restrictNormalHom_surjective _) χ
  refine ⟨N, hPN, originalRelationFreeGroupChange τ B ≫ β, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro r
  exact congrArg (fun m => m.hom ((originalRelationGroupChange τ B).hom r)) hrel

end
end Dubon2026
