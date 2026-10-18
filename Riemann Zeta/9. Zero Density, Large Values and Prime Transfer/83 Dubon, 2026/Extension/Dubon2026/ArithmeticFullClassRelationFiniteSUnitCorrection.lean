import Dubon2026.ArithmeticSPlaceRelationFiniteSUnitCorrection
import Dubon2026.ArithmeticSourceClassRelationExtension

/-! Consume prime saturation, source-class descent and the projective
S-place lift. A full-class extension of the actual relation now yields
an original S-unit correction at a finite arithmetic field. This removes
the source-class lift assumption in the DUB-17 reverse-localization chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  [IsAlgClosure K Ω] (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 K) ∣ a)
  (B : Rep.{0} ℤ Gal(P/K)) [Finite B] (hB : ∀ b : B, q • b = 0)

include hqa hB in
/-- A full-class extension gives an actual finite S-unit relation correction,
with source-class saturation and all finite descent supplied by proved results. -/
theorem arithmeticFullClassRelation_exists_finite_SUnit_correction :
    let πP : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) →* Gal(P/K) :=
      AlgEquiv.restrictNormalHom P
    ∀ (ψ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep K Ω a ha P)
      (f : Rep.res πP (Rep.free ℤ Gal(P/K) B) ⟶ arithmeticClassesModOutsideColimitRep K Ω a ha),
      (Rep.resFunctor πP).map (originalRelationInclusion B) ≫ f =
        (Rep.resFunctor πP).map (ψ ≫ arithmeticSPlaceFiniteStageQuotient K Ω a ha P) ≫
          coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P ≫
            arithmeticSourceClassColimitComparison K Ω a ha →
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
  let φ := (Rep.resFunctor πP).map (ψ ≫ arithmeticSPlaceFiniteStageQuotient K Ω a ha P) ≫
    coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition K Ω a ha) P
  have hlift := arithmeticSourceClassRelation_extension_lifts K Ω a ha q hqa P B hB
  dsimp only [originalRelationShortComplex, ShortComplex.map, Rep.resFunctor] at hlift
  obtain ⟨fS, _, hS⟩ := hlift φ f hf
  exact arithmeticSPlaceRelation_exists_finite_SUnit_correction K Ω a ha P B ψ fS hS

end
end Dubon2026
