import Dubon2026.AffineSchemeCoordinateGroupObject
import Dubon2026.CoordinateGroupObjectPointEquiv

/-! # Recovered Hopf points agree with the actual original affine scheme group and pullbacks -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj CategoryTheory.Obj
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The original scheme fiber products. -/
local instance recoveredPointSchemeCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Retain the original fiber-product monoidal structure explicitly. -/
local instance recoveredPointSchemeMonoidal : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  recoveredPointSchemeCartesian.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- The original symmetry of scheme fiber products. -/
local instance recoveredPointSchemeBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Compose the actual convolution-to-coordinate-group comparison with the group-valued
Yoneda comparison of the original affine presentation. This identifies the recovered Hopf
points with the same original scheme points as groups, not merely as sets. -/
def affineSchemeRecoveredHopfPointEquiv
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X)
    (B : CommAlgCat.{u} R) :
    letI := affineSchemeCoordinateGroupObject G e
    letI := coordinateGroupObjectHopfAlgebra (op (CommAlgCat.of R A))
    WithConv (A →ₐ[R] B) ≃*
      ((coordinateRelativeSpec (R := R)).obj (op B) ⟶ G.X) := by
  letI := affineSchemeCoordinateGroupObject G e
  letI := coordinateGroupObjectHopfAlgebra (op (CommAlgCat.of R A))
  let E : (op B ⟶ op (CommAlgCat.of R A)) ≃*
      ((coordinateRelativeSpec (R := R)).obj (op B) ⟶ G.X) :=
    ((yonedaGrpObjIsoOfRepresentableBy (op (CommAlgCat.of R A))
      (affineSchemeCoordinatePointPresheaf G ⋙ forget₂ CommGrpCat GrpCat)
      (affineSchemeCoordinatePointRepresentable G e)).app (op (op B))).groupIsoToMulEquiv
  exact (coordinateGroupObjectPointEquiv (op (CommAlgCat.of R A)) B).trans E

/-- The recovered group point is exactly the relative spectrum of the same original
coordinate homomorphism followed by the original affine presentation. -/
theorem affineSchemeRecoveredHopfPointEquiv_apply
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X)
    (B : CommAlgCat.{u} R) :
    letI := affineSchemeCoordinateGroupObject G e
    letI := coordinateGroupObjectHopfAlgebra (op (CommAlgCat.of R A))
    ∀ p : WithConv (A →ₐ[R] B),
      affineSchemeRecoveredHopfPointEquiv G e B p =
        (coordinateRelativeSpec (R := R)).map (CommAlgCat.ofHom p.ofConv).op ≫ e.hom := by
  intro p
  rfl

/-- Original coefficient composition agrees with actual pullback of the original scheme
point. Specializing to the original field automorphisms gives its original Galois action. -/
theorem affineSchemeRecoveredHopfPointEquiv_coefficient
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X)
    (B C : CommAlgCat.{u} R) (f : B ⟶ C) :
    letI := affineSchemeCoordinateGroupObject G e
    letI := coordinateGroupObjectHopfAlgebra (op (CommAlgCat.of R A))
    ∀ p : WithConv (A →ₐ[R] B),
      affineSchemeRecoveredHopfPointEquiv G e C (commutativeHopfPointsMap f.hom p) =
        (coordinateRelativeSpec (R := R)).map f.op ≫ affineSchemeRecoveredHopfPointEquiv G e B p := by
  intro p
  rw [affineSchemeRecoveredHopfPointEquiv_apply, affineSchemeRecoveredHopfPointEquiv_apply]
  change (coordinateRelativeSpec (R := R)).map (f.op ≫ (CommAlgCat.ofHom p.ofConv).op) ≫ e.hom =
    (coordinateRelativeSpec (R := R)).map f.op ≫
      ((coordinateRelativeSpec (R := R)).map (CommAlgCat.ofHom p.ofConv).op ≫ e.hom)
  rw [Functor.map_comp, Category.assoc]

end
end Dubon2026
