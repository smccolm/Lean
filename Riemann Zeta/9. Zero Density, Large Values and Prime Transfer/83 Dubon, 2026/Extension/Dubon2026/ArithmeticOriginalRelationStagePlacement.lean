import Dubon2026.UnramifiedUnionFiniteStage
import Dubon2026.OriginalArithmeticRelationScalarCriterion

/-! # Place the actual class-colimit stage in the original scalar criterion

The relation descent uses finite fields inside the arithmetic union. The
scalar criterion uses original finite subfields of the ambient closure.
The proved literal stage embedding joins these two interfaces, retaining
the coefficient through the actual Galois restriction. This removes the
field-placement step on DUB-17's source-to-finite-pairing chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Keep the original arithmetic union's rational inclusion. -/
local instance relationPlacementUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Keep every original finite stage's displayed rational algebra. -/
local instance relationPlacementStageAlgebra {L : Type} [Field L] [Algebra ℚ L]
    (F : FiniteGaloisIntermediateField ℚ L) : Algebra ℚ F := F.algebra'

/-- Restrict the actual coefficient along the embedded original stage's
literal Galois map, retaining the supplied field embedding as its algebra. -/
abbrev arithmeticOriginalStageRestrictedCoefficient
    (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (F : OriginalUnramifiedGaloisStage (Ω := Ω) a) (i : P →ₐ[ℚ] F.val)
    (B : Rep.{0} ℤ Gal(P/ℚ)) : Rep.{0} ℤ Gal(F.val/ℚ) := by
  letI : Algebra P F.val := i.toAlgebra
  letI : Module P F.val := i.toAlgebra.toModule
  letI : SMul P F.val := i.toAlgebra.toSMul
  letI : IsScalarTower ℚ P F.val := IsScalarTower.of_algHom i
  exact Rep.res (AlgEquiv.restrictNormalHom P : Gal(F.val/ℚ) →* Gal(P/ℚ)) B

/-- Every actual finite class-colimit stage reaches a constructed original
stage carrying its exact scalar relation criterion; the intervening field
embedding agrees with the original ambient inclusion. -/
theorem arithmeticClassStage_exists_original_scalar_relation_criterion
    (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ F : OriginalUnramifiedGaloisStage (Ω := Ω) a, ∃ i : P →ₐ[ℚ] F.val,
      (∀ x : P, (i x : Ω) = (x.val : Ω)) ∧
      let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
      ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
        ∃ hFN : F.val.toIntermediateField ≤ N.val.toIntermediateField,
          letI : Algebra F.val N.val := (IntermediateField.inclusion hFN).toRingHom.toAlgebra
          letI : IsScalarTower ℚ F.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hFN)
          let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
            (originalIntegerMap_ne_zero (L := N.val) a ha)
          let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
          let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
          let BN := Rep.res (AlgEquiv.restrictNormalHom F.val : Gal(N.val/ℚ) →* Gal(F.val/ℚ)) BF
          ∃ d : OriginalRelationPrimePairingData BN C p,
            ∀ ψ : originalRelationModule BN ⟶ C,
              (∀ y, d.readout ψ y = 0) ↔
                ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ := by
  obtain ⟨F, i, hi⟩ := originalUnramifiedUnion_finite_subextension_embeds_stage a ha P.toIntermediateField
  let BF := arithmeticOriginalStageRestrictedCoefficient Ω a P F i B
  refine ⟨F, i, hi, ?_⟩
  exact originalUnramifiedStage_exists_scalar_relation_criterion Ω a ha F p hp2 hpa BF hB

end
end Dubon2026
