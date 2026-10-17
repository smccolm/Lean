import Dubon2026.OriginalRelationExtensionObstruction
import Dubon2026.OriginalCoefficientNormCohomology

/-! # A literal norm witness annihilates the original relation obstruction

This is the forward direction of the precise norm criterion used in the
finite class/Ext argument for DUB-17. It consumes the actual additive map
and sum of conjugates, using existing integer scalar uniqueness to retain
the original coefficient modules. The arithmetic converse remains open.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (A C : Rep.{0} ℤ G)

/-- The original additive coefficient map is integer-linear for the original representation module structures. -/
def originalCoefficientAdditiveLinearMap (η : A →+ C) : A →ₗ[ℤ] C where
  toFun := η
  map_add' := η.map_add
  map_smul' n x := by
    change η (@SMul.smul ℤ A A.hV2.toSMul n x) = @SMul.smul ℤ C C.hV2.toSMul n (η x)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul, map_zsmul]

variable [Fintype G] (B : Rep.{0} ℤ G)

/-- A genuine sum-of-conjugates witness kills the actual relation connecting obstruction, without any class-formation or duality hypothesis. -/
theorem originalRelationExtensionObstruction_zero_of_norm
    (φ : originalRelationModule B ⟶ C) (η : originalRelationModule B →+ C)
    (hη : ∀ x : originalRelationModule B,
      φ.hom x = ∑ g : G, C.ρ g (η ((originalRelationModule B).ρ g⁻¹ x))) :
    originalRelationExtensionObstruction B C φ = 0 := by
  let f := originalCoefficientAdditiveLinearMap (originalRelationModule B) C η
  have he : φ = originalCoefficientNormMorphism (originalRelationModule B) C f := by
    apply Rep.hom_ext
    ext x
    exact (hη x).trans (originalCoefficientNormMorphism_apply (originalRelationModule B) C f x).symm
  unfold originalRelationExtensionObstruction
  erw [he, originalCoefficientNormMorphism_positive_map_zero (originalRelationModule B) C f 1,
    Limits.comp_zero]

end
end Dubon2026
