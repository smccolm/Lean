import Dubon2026.HopfCoordinateAffineGroupScheme
import Dubon2026.CoordinateGroupObjectHopfAlgebra

/-! # Recover the genuine coordinate group object from an original affine group scheme

The input is an actual affine coordinate presentation over the original base. The point
groups and their representation by those coordinates are constructed from the same scheme.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj
universe u
variable {R : Type u} [CommRing R]

/-- Use the original fiber products in the category of schemes over the base. -/
local instance affinePointSchemeCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Fix the same original fiber-product monoidal structure under the full import graph. -/
local instance affinePointSchemeMonoidal : MonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  affinePointSchemeCartesian.toSemiCartesianMonoidalCategory.toMonoidalCategory

/-- Use the original symmetry of those fiber products. -/
local instance affinePointSchemeBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

private def coordinatePresentationFullyFaithful : (coordinateRelativeSpec (R := R)).FullyFaithful := by
  unfold coordinateRelativeSpec
  exact (Functor.FullyFaithful.ofFullyFaithful
    (commAlgCatEquivUnder (CommRingCat.of R)).op.functor).comp
      ((Functor.FullyFaithful.ofFullyFaithful
        (Over.opEquivOpUnder (CommRingCat.of R)).inverse).comp
          (Functor.FullyFaithful.ofFullyFaithful
            (Over.post Scheme.Spec (X := op (CommRingCat.of R)))))

/-- The actual group scheme supplies its genuine commutative groups of points on each
original relative affine spectrum, with pullback along the original coefficient maps. -/
def affineSchemeCoordinatePointPresheaf (G : CommGrp (Over (Spec (CommRingCat.of R)))) :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj B := CommGrpCat.of ((coordinateRelativeSpec (R := R)).obj B.unop ⟶ G.X)
  map f := CommGrpCat.ofHom
    (((yonedaGrpObj G.X).map ((coordinateRelativeSpec (R := R)).map f.unop).op).hom)
  map_id B := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro p
    change (coordinateRelativeSpec (R := R)).map (𝟙 B.unop) ≫ p = p
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro p
    change (coordinateRelativeSpec (R := R)).map (g.unop ≫ f.unop) ≫ p =
      (coordinateRelativeSpec (R := R)).map g.unop ≫
        ((coordinateRelativeSpec (R := R)).map f.unop ≫ p)
    rw [Functor.map_comp, Category.assoc]

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The specified actual affine coordinate presentation represents precisely the original
scheme-point presheaf, via fully faithful relative spectrum and the original presentation map. -/
def affineSchemeCoordinatePointRepresentable
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X) :
    (affineSchemeCoordinatePointPresheaf G ⋙ forget CommGrpCat).RepresentableBy
      (op (CommAlgCat.of R A)) where
  homEquiv := coordinatePresentationFullyFaithful.homEquiv.trans e.homToEquiv
  homEquiv_comp f g := by
    change (coordinateRelativeSpec (R := R)).map (f ≫ g) ≫ e.hom =
      (coordinateRelativeSpec (R := R)).map f ≫
        ((coordinateRelativeSpec (R := R)).map g ≫ e.hom)
    rw [Functor.map_comp, Category.assoc]

/-- The constructed representing bijection sends an original coordinate morphism to exactly
its original relative spectrum morphism followed by the specified original scheme presentation. -/
theorem affineSchemeCoordinatePointRepresentable_apply
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X)
    (B : (CommAlgCat.{u} R)ᵒᵖ) (f : B ⟶ op (CommAlgCat.of R A)) :
    (affineSchemeCoordinatePointRepresentable G e).homEquiv f =
      (coordinateRelativeSpec (R := R)).map f ≫ e.hom := by
  rfl

/-- The same original affine coordinates become a genuine commutative group object in the
canonical tensor-product opposite algebra category, by the constructed original point presheaf. -/
@[implicit_reducible]
def affineSchemeCoordinateGroupObject
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X) :
    CommGrpObj (op (CommAlgCat.of R A)) :=
  CommGrpObj.ofRepresentableBy _ (affineSchemeCoordinatePointPresheaf G)
    (affineSchemeCoordinatePointRepresentable G e)

/-- An actual affine presentation of the original commutative group scheme constructs its
coordinate group object rather than assuming an algebra-side group or Hopf structure. -/
theorem affineSchemeCoordinateGroupObject_exists
    (G : CommGrp (Over (Spec (CommRingCat.of R))))
    (e : (coordinateRelativeSpec (R := R)).obj (op (CommAlgCat.of R A)) ≅ G.X) :
    Nonempty (CommGrpObj (op (CommAlgCat.of R A))) := by
  exact ⟨affineSchemeCoordinateGroupObject G e⟩

end
end Dubon2026
