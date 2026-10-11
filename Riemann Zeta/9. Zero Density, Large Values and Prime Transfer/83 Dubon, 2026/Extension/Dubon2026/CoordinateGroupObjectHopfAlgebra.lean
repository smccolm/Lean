import Mathlib.Algebra.Category.CommBialgCat
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.RingTheory.HopfAlgebra.Basic

/-! # Genuine Hopf coordinates of an original group object in opposite commutative algebras

Use the pinned tensor-product monoidal structure and its actual monoid-to-bialgebra
construction. The two original group inverse identities provide the antipode axioms.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite MonObj MonoidalCategory
open scoped TensorProduct

universe u
variable {R : Type u} [CommRing R]

private theorem coordinateTensorLiftLeftLinear {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] A) :
    (Algebra.TensorProduct.lift f (AlgHom.id R A) (fun _ _ => .all _ _)).toLinearMap =
      LinearMap.mul' R A ∘ₗ f.toLinearMap.rTensor A := by
  ext a b
  rfl

private theorem coordinateTensorLiftRightLinear {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] A) :
    (Algebra.TensorProduct.lift (AlgHom.id R A) f (fun _ _ => .all _ _)).toLinearMap =
      LinearMap.mul' R A ∘ₗ f.toLinearMap.lTensor A := by
  ext a b
  rfl

variable (G : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj G]

/-- The same original coordinate algebra is a Hopf algebra. Its bialgebra is the pinned
construction from the actual multiplication and identity morphisms; its antipode is exactly
the original group inverse on coordinates, with both identities derived from the group laws. -/
abbrev coordinateGroupObjectHopfAlgebra : HopfAlgebra R G.unop where
  toBialgebra := inferInstance
  antipode := ι[G].unop.hom.toLinearMap
  mul_antipode_rTensor_comul := by
    have h := congrArg (fun f : G ⟶ G => f.unop.hom.toLinearMap) (GrpObj.left_inv G)
    change (Algebra.TensorProduct.lift ι[G].unop.hom (AlgHom.id R G.unop)
        (fun _ _ => .all _ _)).toLinearMap ∘ₗ μ[G].unop.hom.toLinearMap =
      (Algebra.linearMap R G.unop) ∘ₗ η[G].unop.hom.toLinearMap at h
    rw [coordinateTensorLiftLeftLinear] at h
    exact h
  mul_antipode_lTensor_comul := by
    have h := congrArg (fun f : G ⟶ G => f.unop.hom.toLinearMap) (GrpObj.right_inv G)
    change (Algebra.TensorProduct.lift (AlgHom.id R G.unop) ι[G].unop.hom
        (fun _ _ => .all _ _)).toLinearMap ∘ₗ μ[G].unop.hom.toLinearMap =
      (Algebra.linearMap R G.unop) ∘ₗ η[G].unop.hom.toLinearMap at h
    rw [coordinateTensorLiftRightLinear] at h
    exact h

/-- The constructed Hopf antipode evaluates precisely the original inverse coordinate map. -/
theorem coordinateGroupObjectHopfAlgebra_antipode (a : G.unop) :
    letI := coordinateGroupObjectHopfAlgebra G
    HopfAlgebra.antipode R a = ι[G].unop.hom a := by
  rfl

/-- Commutativity of the original group object yields cocommutativity of the same actual
coordinate coalgebra by applying the original opposite algebra morphism comparison. -/
theorem coordinateGroupObjectHopfAlgebra_isCocomm [IsCommMonObj G] :
    letI := coordinateGroupObjectHopfAlgebra G
    Coalgebra.IsCocomm R G.unop := by
  letI := coordinateGroupObjectHopfAlgebra G
  constructor
  exact congrArg (fun f : G ⊗ G ⟶ G => f.unop.hom.toLinearMap) (IsCommMonObj.mul_comm G)

end
end Dubon2026
