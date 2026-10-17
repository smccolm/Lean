import Dubon2026.ArithmeticFiniteClassHomDescent

/-! # The descended class morphism uses the actual finite Galois group

The pinned surjective-restriction Hom lifting theorem and the actual
Galois tower identity retain the same coefficient map at a finite stage.
This supplies the literal finite-group morphism in the degree-zero term
of DUB-17's class/Ext comparison, without an equivariance certificate.
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

/-- An actual full-class colimit morphism descends above the original
field to a genuine finite-Galois equivariant morphism, retaining every
original coefficient value under the literal colimit inclusion. -/
theorem arithmeticFiniteClassHom_exists_galois_descent
    (φ : Rep.res (AlgEquiv.restrictNormalHom P :
      Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K)) B ⟶
        arithmeticClassesModOutsideColimitRep K Ω a ha) :
    ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      ∃ hPN : P ≤ N,
        letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
        ∃ η : Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B ⟶
            arithmeticClassesModOutsideStageRep K Ω a ha N,
          ∀ b : B, (coefficientRepresentationColimitOf _
            (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) N).hom (η.hom b) =
              φ.hom b := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    originalUnramifiedGaloisUnion_isGalois a
  obtain ⟨N, hPN, ψ, hψ⟩ := arithmeticFiniteClassHom_exists_stage K Ω a ha P B φ
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  letI : IsScalarTower P N (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
    .of_algebraMap_eq' rfl
  letI : IsScalarTower K P N := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(N/K) :=
    AlgEquiv.restrictNormalHom N
  let BN := Rep.res (AlgEquiv.restrictNormalHom P : Gal(N/K) →* Gal(P/K)) B
  let C := arithmeticClassesModOutsideStageRep K Ω a ha N
  let χ : Rep.res π BN ⟶ Rep.res π C := Rep.ofHom {
    toLinearMap := ψ.hom.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro b
      change ψ.hom (B.ρ (AlgEquiv.restrictNormalHom P (AlgEquiv.restrictNormalHom N g)) b) =
        (arithmeticGlobalClassesModOutsideStageRep K Ω a ha N).ρ g (ψ.hom b)
      rw [← IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply P N g]
      exact Rep.hom_comm_apply ψ g b }
  have hπ : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective _
  let η := Rep.liftHomOfSurj π hπ χ
  refine ⟨N, hPN, η, ?_⟩
  intro b
  exact congrArg (fun m => m.hom b) hψ

end
end Dubon2026
