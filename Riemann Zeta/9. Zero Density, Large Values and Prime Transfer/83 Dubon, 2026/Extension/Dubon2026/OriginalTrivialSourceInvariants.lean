import Dubon2026.OriginalCoefficientNormCohomology

/-! # Literal invariant vectors as maps from the original integral line

Evaluation at one identifies actual coefficient morphisms with invariant
vectors and retains their literal norms. This is the model comparison
needed to apply the finite abelian norm index in DUB-17's norm-field step.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module

variable {G : Type} [Group G] (C : Rep.{0} ℤ G)

/-- Evaluation at one identifies actual equivariant maps from the integral line with invariant vectors. -/
def originalTrivialSourceInvariantEquiv :
    (Rep.trivial ℤ G ℤ ⟶ C) ≃ₗ[ℤ] C.ρ.invariants where
  toFun χ := ⟨χ.hom 1, fun g => (Rep.hom_comm_apply χ g 1).symm⟩
  invFun x := Rep.ofHom {
    toLinearMap := LinearMap.toSpanSingleton ℤ C x.val
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro n
      simp only [LinearMap.comp_apply, Representation.trivial_apply, LinearMap.toSpanSingleton_apply]
      exact ((C.ρ g).map_smul n x.val).trans
        (congrArg (C.hV2.smul n) (x.property g)) |>.symm }
  left_inv χ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro n
    change (LinearMap.toSpanSingleton ℤ C (χ.hom 1)) n = χ.hom n
    simpa only [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_one] using
      (χ.hom.toLinearMap.map_smul n (1 : ℤ)).symm
  right_inv x := by
    apply Subtype.ext
    exact LinearMap.toSpanSingleton_apply_one ℤ C x.val
  map_add' _ _ := Subtype.ext rfl
  map_smul' n χ := Subtype.ext (int_smul_eq_zsmul C.hV2 n (χ.hom 1)).symm

variable [Fintype G]

/-- The original group norm as a linear map to the actual invariant submodule. -/
def originalInvariantNormLinear : C →ₗ[ℤ] C.ρ.invariants :=
  C.ρ.norm.codRestrict C.ρ.invariants (fun x g => C.ρ.self_norm_apply g x)

/-- Evaluation of a literal original morphism norm is exactly the actual invariant norm. -/
theorem originalTrivialSourceInvariantEquiv_norm
    (η : Rep.trivial ℤ G ℤ →ₗ[ℤ] C) :
    originalTrivialSourceInvariantEquiv C
      (originalCoefficientNormMorphism (Rep.trivial ℤ G ℤ) C η) =
        originalInvariantNormLinear C (η 1) := by
  apply Subtype.ext
  change (originalCoefficientNormMorphism (Rep.trivial ℤ G ℤ) C η).hom 1 = C.ρ.norm (η 1)
  rw [originalCoefficientNormMorphism_apply]
  simp only [Representation.norm, LinearMap.sum_apply]
  rfl

end
end Dubon2026
