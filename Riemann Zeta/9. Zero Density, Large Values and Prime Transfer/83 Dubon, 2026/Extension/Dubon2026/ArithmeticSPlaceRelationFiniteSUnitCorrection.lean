import Dubon2026.ArithmeticSourceClassExtensionGaloisDescent
import Dubon2026.OriginalSPlaceRelationSUnitCorrection

/-! Consume finite Galois descent and the projective S-place lift on the
same actual idele relation. A colimit source-class extension now gives a
finite original S-unit correction, the input for the arithmetic dual
connecting class in DUB-17's reverse-localization proof. -/
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

/-- The actual idele relation, with a source-class colimit extension,
has an S-unit correction at one finite Galois stage. -/
theorem arithmeticSPlaceRelation_exists_finite_SUnit_correction :
    let πP : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K) :=
      AlgEquiv.restrictNormalHom P
    ∀ (ψ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep K Ω a ha P)
      (f : Rep.res πP (Rep.free ℤ Gal(P/K) B) ⟶ arithmeticSPlaceClassColimitRep K Ω a ha),
      (Rep.resFunctor πP).map (originalRelationInclusion B) ≫ f =
        (Rep.resFunctor πP).map (ψ ≫ arithmeticSPlaceFiniteStageQuotient K Ω a ha P) ≫
          coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P →
      ∃ N : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hPN : P ≤ N,
          letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
          let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
          let ψN := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map ψ ≫
            arithmeticSPlaceFiniteTransition K Ω a ha P N hPN
          ∃ l : Rep.free ℤ Gal(N/K) (Rep.res τ B) ⟶ ArithmeticSPlaceFiniteStageRep K Ω a ha N,
            ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticSUnitFiniteStageRep K Ω a ha N,
              η ≫ arithmeticSPlaceFiniteStagePrincipal K Ω a ha N =
                ψN - originalRelationInclusion (Rep.res τ B) ≫ l := by
  intro πP ψ f hf
  obtain ⟨N, hPN, fN, hN⟩ :=
    arithmeticSourceClassExtension_exists_finite_galois_extension K Ω a ha P B
      (ψ ≫ arithmeticSPlaceFiniteStageQuotient K Ω a ha P) f hf
  letI : Algebra P N := (IntermediateField.inclusion hPN).toAlgebra
  let τ : Gal(N/K) →* Gal(P/K) := AlgEquiv.restrictNormalHom P
  let ψN := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map ψ ≫
    arithmeticSPlaceFiniteTransition K Ω a ha P N hPN
  have hrel : originalRelationInclusion (Rep.res τ B) ≫ fN =
      ψN ≫ arithmeticSPlaceFiniteStageQuotient K Ω a ha N := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    exact (congrArg (fun m => m.hom r) hN).trans
      (arithmeticSPlaceClassFiniteTransition_quotient K Ω a ha P N hPN
        (ψ.hom ((originalRelationGroupChange τ B).hom r)))
  letI : NumberField N := NumberField.of_module_finite K N
  obtain ⟨l, η, _, hη⟩ := originalSPlaceRelation_exists_SUnit_correction K N
    (arithmeticSUnitFiniteStageSupport K Ω a ha N)
    (originalExceptionalIntegerSupport_galoisStable N K a ha) (Rep.res τ B) ψN fN hrel
  exact ⟨N, hPN, l, η, hη⟩

end
end Dubon2026
