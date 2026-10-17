import Dubon2026.OriginalInvariantHomEvaluation
import Dubon2026.OriginalInternalHomPrecomposition
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-! # Actual relation morphism from a free-cover Hom coboundary

A coboundary lift of the original coefficient cocycle restricts to an
equivariant map on the literal relation kernel. No surjectivity of the
dual Hom sequence or integer Ext vanishing for the class coefficient is
needed. This is the shorter relation-representative route for DUB-17.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G : Type} [CommRing R] [Group G]
  (X : ShortComplex (Rep.{0} R G)) (C : Rep.{0} R G)

/-- The original free-cover coboundary restricts to a genuine equivariant
relation morphism, with its exact linear map unchanged. -/
theorem originalRelationHom_exists_of_free_coboundary
    (c : G → (Rep.ihom X.X₃).obj C) (v : (Rep.ihom X.X₂).obj C)
    (hv : ∀ g, ((Rep.ihom X.X₂).obj C).ρ g v - v =
      (originalInternalHomPrecomposition C X.g).hom (c g)) :
    ∃ φ : X.X₁ ⟶ C,
      φ.hom.toLinearMap = (show X.X₂ →ₗ[R] C from v).comp X.f.hom.toLinearMap := by
  let f := originalInternalHomPrecomposition C X.f
  let w := f.hom v
  have hw : ∀ g, ((Rep.ihom X.X₁).obj C).ρ g w = w := by
    intro g
    have he := congrArg f.hom (hv g)
    rw [map_sub, Rep.hom_comm_apply] at he
    have hz : f.hom ((originalInternalHomPrecomposition C X.g).hom (c g)) = 0 := by
      apply LinearMap.ext
      intro x
      change DFunLike.coe (F := X.X₃ →ₗ[R] C) (c g) (X.g.hom (X.f.hom x)) = 0
      have hzero : X.g.hom (X.f.hom x) = 0 :=
        congrArg (fun m : X.X₁ ⟶ X.X₃ => m.hom x) X.zero
      rw [hzero, map_zero]
    exact sub_eq_zero.mp (he.trans hz)
  exact ⟨originalInvariantHomMorphism X.X₁ C ⟨w, hw⟩, rfl⟩

end
end Dubon2026
