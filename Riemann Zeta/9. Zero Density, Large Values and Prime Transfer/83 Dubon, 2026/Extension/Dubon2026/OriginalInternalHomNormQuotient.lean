import Dubon2026.OriginalNormQuotientCohomology

/-! # Original morphisms modulo norms as internal-Hom norm classes

The homology construction for DUB-17 uses the actual internal-Hom
representation. These identities identify its invariant vectors and
literal norm with the already defined original morphism norm quotient.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] (M C : Rep.{0} ℤ G)

/-- An actual equivariant coefficient map is an invariant in the original internal Hom. -/
theorem originalMorphism_internalHom_invariant (χ : M ⟶ C) :
    χ.hom.toLinearMap ∈ ((Rep.ihom M).obj C).ρ.invariants := by
  intro g
  apply LinearMap.ext
  intro x
  change C.ρ g (χ.hom (M.ρ g⁻¹ x)) = χ.hom x
  rw [← Rep.hom_comm_apply, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

variable [Fintype G]

/-- The actual internal-Hom norm is the original coefficient norm morphism on underlying linear maps. -/
theorem originalInternalHom_norm_eq_coefficientNorm (η : M →ₗ[ℤ] C) :
    ((Rep.ihom M).obj C).ρ.norm η =
      (originalCoefficientNormMorphism M C η).hom.toLinearMap := by
  simp only [Representation.norm, LinearMap.sum_apply]
  change (∑ g : G, C.ρ g ∘ₗ η ∘ₗ M.ρ g⁻¹) = _
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply]
  exact (originalCoefficientNormMorphism_apply M C η x).symm

/-- The original morphism norm quotient is zero exactly when the same original internal-Hom invariant has a norm preimage. -/
theorem originalCoefficientNormQuotient_zero_iff_internalHom_norm (χ : M ⟶ C) :
    (Submodule.Quotient.mk χ : OriginalCoefficientNormQuotient M C) = 0 ↔
      ∃ η : (Rep.ihom M).obj C, ((Rep.ihom M).obj C).ρ.norm η = χ.hom.toLinearMap := by
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η, (originalInternalHom_norm_eq_coefficientNorm M C η).trans ?_⟩
    exact congrArg (fun f : M ⟶ C => f.hom.toLinearMap) hη
  · rintro ⟨η, hη⟩
    refine ⟨η, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact (originalInternalHom_norm_eq_coefficientNorm M C η).symm.trans hη

end
end Dubon2026
