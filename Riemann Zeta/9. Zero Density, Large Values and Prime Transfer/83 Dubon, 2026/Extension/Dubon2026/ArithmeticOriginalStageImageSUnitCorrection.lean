import Dubon2026.ArithmeticOriginalStageImageExtensionColimit
import Dubon2026.ArithmeticFullClassRelationFiniteSUnitCorrection

/-! Consume the original ambient-stage extension, its proved colimit
transport, and the finite S-unit correction on the identical idele relation.
This removes every supplied source-class lift and finite-stage correction
from DUB-17's Cartier-to-global-S-unit dependency chain. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] relationTransportUnionAlgebra relationTransportStageAlgebra

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
  (a : 𝓞 ℚ) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (N : OriginalUnramifiedGaloisStage (Ω := Ω) a)
  (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (B : Rep.{0} ℤ Gal(originalUnramifiedStageInUnion a N / ℚ)) [Finite B]
  (hB : ∀ b : B, q • b = 0)

/-- A finite original S-unit correction of the given image-stage idele relation. -/
abbrev ArithmeticOriginalImageFiniteSUnitCorrectionResult
    (ψ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ Ω a ha
      (originalUnramifiedStageInUnion a N)) : Prop :=
    let M := originalUnramifiedStageInUnion a N
      ∃ L : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a),
        ∃ hML : M ≤ L,
          letI : Algebra M L := (IntermediateField.inclusion hML).toAlgebra
          letI : Module M L := (IntermediateField.inclusion hML).toAlgebra.toModule
          letI : SMul M L := (IntermediateField.inclusion hML).toAlgebra.toSMul
          let τ : Gal(L/ℚ) →* Gal(M/ℚ) := AlgEquiv.restrictNormalHom M
          let ψL := originalRelationGroupChange τ B ≫ (Rep.resFunctor τ).map ψ ≫
            arithmeticSPlaceFiniteTransition ℚ Ω a ha M L hML
          ∃ l : Rep.free ℤ Gal(L/ℚ) (Rep.res τ B) ⟶ ArithmeticSPlaceFiniteStageRep ℚ Ω a ha L,
            ∃ η : originalRelationModule (Rep.res τ B) ⟶ arithmeticSUnitFiniteStageRep ℚ Ω a ha L,
              η ≫ arithmeticSPlaceFiniteStagePrincipal ℚ Ω a ha L =
                ψL - originalRelationInclusion (Rep.res τ B) ≫ l

include hqa hB in
/-- The original class extension of an actual image-stage idele relation
constructs a finite original S-unit correction of that same relation. -/
theorem arithmeticOriginalStageImage_exists_finite_SUnit_correction :
    let M := originalUnramifiedStageInUnion a N
    let e := originalUnramifiedStageInUnionEquiv a N
    let BN := arithmeticOriginalStageRestrictedCoefficient Ω a M N e.symm.toAlgHom B
    ∀ (ψ : originalRelationModule B ⟶ ArithmeticSPlaceFiniteStageRep ℚ Ω a ha M)
      (f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ arithmeticOriginalStageClassRep Ω a ha N),
      originalRelationInclusion BN ≫ f =
        arithmeticOriginalStageRelationClassTransport Ω a ha M N e.symm.toAlgHom B
          (ψ ≫ arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha M ≫
            arithmeticSourceClassStageComparison ℚ Ω a ha M) →
      ArithmeticOriginalImageFiniteSUnitCorrectionResult Ω a ha N B ψ := by
  intro M e BN ψ f hf
  let φ := ψ ≫ arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha M ≫
    arithmeticSourceClassStageComparison ℚ Ω a ha M
  obtain ⟨fG, hG⟩ := arithmeticOriginalStageImage_extension_to_colimit Ω a ha N B φ f hf
  let πM : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(M/ℚ) :=
    AlgEquiv.restrictNormalHom M
  have hfull : (Rep.resFunctor πM).map (originalRelationInclusion B) ≫ fG =
      (Rep.resFunctor πM).map (ψ ≫ arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha M) ≫
        coefficientRepresentationColimitOf _ (arithmeticGlobalSPlaceClassStageTransition ℚ Ω a ha) M ≫
          arithmeticSourceClassColimitComparison ℚ Ω a ha := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro r
    exact (congrArg (fun m => m.hom r) hG).trans
      (arithmeticSourceClassColimitComparison_of ℚ Ω a ha M
        ((arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha M).hom (ψ.hom r))).symm
  exact arithmeticFullClassRelation_exists_finite_SUnit_correction ℚ Ω a ha M q hqa B hB ψ fG hfull

end
end Dubon2026
