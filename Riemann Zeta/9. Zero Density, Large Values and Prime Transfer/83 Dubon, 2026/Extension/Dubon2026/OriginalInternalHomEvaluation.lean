import Dubon2026.OriginalInternalHomPrecomposition

/-! # Original evaluation for the actual dual relation sequence

Literal evaluation and precomposition supply the pairings and compatibility
identities required by the existing cup/connecting theorem. This serves
DUB-17's relation-to-source-duality comparison with the original coefficients.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G : Type} [CommRing R] [Group G] (A B C : Rep.{0} R G)

/-- Evaluate an original linear Hom coefficient on the original element. -/
def originalInternalHomEvaluation : A →ₗ[R] (Rep.ihom A).obj C →ₗ[R] C where
  toFun a := {
    toFun := fun η => (show A →ₗ[R] C from η) a
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  map_add' a b := by
    apply LinearMap.ext
    intro η
    exact (show A →ₗ[R] C from η).map_add a b
  map_smul' r a := by
    apply LinearMap.ext
    intro η
    exact (show A →ₗ[R] C from η).map_smul r a

/-- Original evaluation intertwines the actual coefficient and conjugate Hom actions. -/
theorem originalInternalHomEvaluation_equivariant (g : G) (a : A)
    (η : (Rep.ihom A).obj C) :
    originalInternalHomEvaluation A C (A.ρ g a) (((Rep.ihom A).obj C).ρ g η) =
      C.ρ g (originalInternalHomEvaluation A C a η) := by
  change A →ₗ[R] C at η
  change C.ρ g (η (A.ρ g⁻¹ (A.ρ g a))) = C.ρ g (η a)
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The actual dual map is adjoint to the original coefficient morphism under evaluation. -/
theorem originalInternalHomEvaluation_precomposition (f : A ⟶ B) (a : A)
    (η : (Rep.ihom B).obj C) :
    originalInternalHomEvaluation B C (f.hom a) η =
      originalInternalHomEvaluation A C a ((originalInternalHomPrecomposition C f).hom η) := rfl

end
end Dubon2026
