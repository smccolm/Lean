import Dubon2026.OriginalRationalFullOrderClass
import Dubon2026.OriginalArithmeticStageRelationExtension

/-! # The constructed original arithmetic relation-extension criterion

The original norm-root stage is retained. Its full-order original class is
now constructed for its actual, possibly mixed, degree. This removes the
last supplied class-field premise of the existing finite relation criterion
on DUB-17's finite class/Ext to reverse-localization dependency chain.
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
local instance constructedStageRelationRationalAlgebra {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (F : FiniteGaloisIntermediateField ℚ Ω) : Algebra ℚ F := F.algebra'

/-- At a constructed stage above the original coefficient stage,
the actual zero-obstruction/extension equivalence has its original
full-order class constructed. The norm roots, kernel action, support
unramifiedness and all comparison data are constructed. -/
theorem originalUnramifiedStage_exists_constructed_relation_criterion
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (a : 𝓞 ℚ) (ha : a ≠ 0)
    (P : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hpa : (p : 𝓞 ℚ) ∣ a)
    (B : Rep.{0} ℤ Gal(P.val/ℚ)) [Finite B] (hB : ∀ b : B, p • b = 0) :
    ∃ N : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      ∃ hPN : P.val.toIntermediateField ≤ N.val.toIntermediateField,
        letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
        letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
        let T := originalExceptionalIntegerSupport N.val (algebraMap (𝓞 ℚ) (𝓞 N.val) a)
          (originalIntegerMap_ne_zero (L := N.val) a ha)
        let hT := originalExceptionalIntegerSupport_galoisStable N.val ℚ a ha
        let C := originalIdeleClassesModOutsideRep ℚ N.val T hT
        let BN := Rep.res (AlgEquiv.restrictNormalHom P.val : Gal(N.val/ℚ) →* Gal(P.val/ℚ)) B
        ∀ χ : originalRelationModule BN ⟶ C,
            originalRelationExtensionObstruction BN C χ = 0 ↔
              ∃ f : Rep.free ℤ Gal(N.val/ℚ) BN ⟶ C, originalRelationInclusion BN ≫ f = χ := by
  obtain ⟨N, hPN, hcriterion⟩ :=
    originalUnramifiedStage_exists_relation_criterion Ω a ha P p hp2 hpa B hB
  refine ⟨N, hPN, ?_⟩
  letI : Algebra P.val N.val := (IntermediateField.inclusion hPN).toRingHom.toAlgebra
  letI : IsScalarTower ℚ P.val N.val := IsScalarTower.of_algHom (IntermediateField.inclusion hPN)
  obtain ⟨u, hu⟩ := originalRationalNumberField_exists_full_order_class_of_algebra N.val
  exact hcriterion u hu

end
end Dubon2026
