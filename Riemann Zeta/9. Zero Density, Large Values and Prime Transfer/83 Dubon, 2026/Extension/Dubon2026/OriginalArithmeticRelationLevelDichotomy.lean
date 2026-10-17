import Dubon2026.OriginalArithmeticConstructedRelationExtension
import Dubon2026.OriginalRelationGroupChange
import Dubon2026.OriginalRationalExceptionalClassTransition

/-! # Detect nonextension at the actual constructed arithmetic level

The original relation morphism is carried by the literal field-group map
and the proved exceptional-support class transition. The constructed stage
criterion gives either an actual extension or an original H1 class detecting
its obstruction. This is the finite-level input to DUB-17's source class
duality and reverse H1 localization; no comparison map is supplied.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul

/-- Use the actual stage inclusion as the rational algebra throughout
the assembled field towers and coefficient restrictions. -/
local instance levelDichotomyRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- At a constructed stage above the original coefficient stage,
each original relation morphism either extends after the canonical
transition or has a nonzero obstruction detected by an actual H1 class.
The enlarged field, generator, norm roots and comparison maps are constructed. -/
theorem originalUnramifiedStage_exists_relation_level_dichotomy
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    let S := originalExceptionalIntegerSupport P.val (algebraMap (𝓞 ℚ) (𝓞 P.val) a)
      (originalIntegerMap_ne_zero (L := P.val) a ha)
    let hS := originalExceptionalIntegerSupport_galoisStable P.val ℚ a ha
    let CP := originalIdeleClassesModOutsideRep ℚ P.val S hS
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∀ φ : originalRelationModule B ⟶ CP,
          let π : Gal(N.val/ℚ) →* Gal(P.val/ℚ) := AlgEquiv.restrictNormalHom P.val
          let ψ := originalRelationGroupChange π B ≫ (Rep.resFunctor π).map φ ≫
            originalRationalExceptionalClassTransition P.val N.val a ha
          (∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ) ∨
            ∃ y : groupCohomology BN 1, (originalRelationExtensionObstruction BN C ψ).hom y ≠ 0 := by
  obtain ⟨N, hPN, hcriterion⟩ :=
    originalUnramifiedStage_exists_constructed_relation_criterion Ω a ha P p hp2 hpa B hB
  refine ⟨N, hPN, ?_⟩
  letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
    (originalIntegerMap_ne_zero (L := N.val) a ha)
  let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
  let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
  let π : Gal(N.val/ℚ) →* Gal(P.val/ℚ) := AlgEquiv.restrictNormalHom P.val
  let BN := Rep.res π B
  dsimp only
  intro φ
  let ψ : originalRelationModule BN ⟶ C := originalRelationGroupChange π B ≫
    (Rep.resFunctor π).map φ ≫ originalRationalExceptionalClassTransition P.val N.val a ha
  change (∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = ψ) ∨
    ∃ y : groupCohomology BN 1, (originalRelationExtensionObstruction BN C ψ).hom y ≠ 0
  by_cases hz : originalRelationExtensionObstruction BN C ψ = 0
  · exact Or.inl ((hcriterion ψ).mp hz)
  · right
    by_contra hn
    apply hz
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    exact not_not.mp (fun hy => hn ⟨y, hy⟩)

end
end Dubon2026
