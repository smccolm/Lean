import Dubon2026.CoordinateGroupObjectHopfAlgebra
import Dubon2026.CommutativeHopfPointsCoefficientChange

/-! # The recovered coordinate Hopf points are the original categorical group points -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite MonObj WithConv
open scoped CategoryTheory.MonObj
universe u
variable {R : Type u} [CommRing R]
variable (G : (CommAlgCat.{u} R)ᵒᵖ) [GrpObj G]

/-- The actual original coordinate-point bijection preserves multiplication: the original
categorical product law is tensor lifting followed by the original coordinate comultiplication,
which is exactly the pinned convolution formula for the constructed Hopf algebra. -/
def coordinateGroupObjectPointEquiv (B : CommAlgCat.{u} R) :
    letI := coordinateGroupObjectHopfAlgebra G
    WithConv (G.unop →ₐ[R] B) ≃* (op B ⟶ G) := by
  letI := coordinateGroupObjectHopfAlgebra G
  refine
    { toFun := fun p => (CommAlgCat.ofHom p.ofConv).op
      invFun := fun f => toConv f.unop.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := ?_ }
  intro p q
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  exact AlgHom.convMul_apply p q a

/-- The actual group comparison retains evaluation on every original coordinate. -/
theorem coordinateGroupObjectPointEquiv_apply (B : CommAlgCat.{u} R) :
    letI := coordinateGroupObjectHopfAlgebra G
    ∀ (p : WithConv (G.unop →ₐ[R] B)) (a : G.unop),
      (coordinateGroupObjectPointEquiv G B p).unop.hom a = p a := by
  intro p a
  rfl

/-- Original coefficient composition is exactly original categorical pullback of the same
point. This comparison therefore retains the action of every original coefficient automorphism. -/
theorem coordinateGroupObjectPointEquiv_coefficient (B C : CommAlgCat.{u} R) (f : B ⟶ C) :
    letI := coordinateGroupObjectHopfAlgebra G
    ∀ p : WithConv (G.unop →ₐ[R] B),
      coordinateGroupObjectPointEquiv G C (commutativeHopfPointsMap f.hom p) =
        f.op ≫ coordinateGroupObjectPointEquiv G B p := by
  intro p
  rfl

end
end Dubon2026
