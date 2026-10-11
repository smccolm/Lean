import Dubon2026.HopfCoordinateAffineGroupScheme

/-! # The original convolution points are the actual affine group-scheme points -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj CategoryTheory.Obj

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A]

/-- The same Cartesian structure on the original coordinate category. -/
local instance pointGroupCoordinateCartesian : CartesianMonoidalCategory ((CommAlgCat.{u} R)ᵒᵖ) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

/-- The same actual symmetry of coordinate products. -/
local instance pointGroupCoordinateBraided : BraidedCategory ((CommAlgCat.{u} R)ᵒᵖ) :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- The same Cartesian structure on the original scheme over category. -/
local instance pointGroupSchemeCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- The same actual symmetry of scheme fiber products. -/
local instance pointGroupSchemeBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- The same actual braided relative spectrum functor. -/
local instance pointGroupSpecBraided : (coordinateRelativeSpec (R := R)).Braided :=
  affineGroupRelativeSpecBraided

/-- Relative spectrum is fully faithful on the original coordinate category. -/
private def originalRelativeSpecFullyFaithful : (coordinateRelativeSpec (R := R)).FullyFaithful := by
  unfold coordinateRelativeSpec
  exact (Functor.FullyFaithful.ofFullyFaithful
    (commAlgCatEquivUnder (CommRingCat.of R)).op.functor).comp
      ((Functor.FullyFaithful.ofFullyFaithful
        (Over.opEquivOpUnder (CommRingCat.of R)).inverse).comp
          (Functor.FullyFaithful.ofFullyFaithful
            (Over.post Scheme.Spec (X := op (CommRingCat.of R)))))

/-- Use the constructed group object on the actual original coordinates. -/
local instance pointGroupCoordinateObject : CommGrpObj (op (CommAlgCat.of R A)) :=
  hopfCoordinateCommutativeGroupObject

/-- Original coordinate-valued points retain their genuine convolution group. -/
local instance affineOriginalPointGroup (B : CommAlgCat.{u} R) :
    CommGroup (WithConv (A →ₐ[R] B)) :=
  { commutativeHopfPointsGroup with mul_comm := mul_comm }

/-- The literal original convolution group is isomorphic to the actual group of morphisms from the same value algebra's spectrum to the constructed group scheme, over the original base. Representability proves the source group law; fully faithful monoidal relative spectrum transports that same law. -/
def hopfAffineSchemePointGroupEquiv (B : CommAlgCat.{u} R) :
    WithConv (A →ₐ[R] B) ≃*
      ((coordinateRelativeSpec (R := R)).obj (op B) ⟶
        (hopfCoordinateAffineGroupScheme (R := R) (A := A)).X) := by
  let e : (op B ⟶ op (CommAlgCat.of R A)) ≃* WithConv (A →ₐ[R] B) :=
    ((yonedaGrpObjIsoOfRepresentableBy (op (CommAlgCat.of R A))
      (hopfCoordinateCommutativeGroupPresheaf (R := R) (A := A) ⋙ forget₂ CommGrpCat GrpCat)
      hopfCoordinateCommutativeGroupPresheafRepresentable).app (op (op B))).groupIsoToMulEquiv
  exact e.symm.trans (Functor.FullyFaithful.homMulEquiv
    (coordinateRelativeSpec (R := R)) originalRelativeSpecFullyFaithful)

/-- The actual scheme point attached to the original algebra point is exactly the spectrum of that original ring homomorphism. -/
theorem hopfAffineSchemePointGroupEquiv_apply (B : CommAlgCat.{u} R)
    (p : WithConv (A →ₐ[R] B)) :
    (hopfAffineSchemePointGroupEquiv B p).left =
      Spec.map (CommRingCat.ofHom p.ofConv.toRingHom) := by
  rfl

/-- Original composition on point values is the genuine pullback of that same scheme point along the original spectrum map. -/
theorem hopfAffineSchemePointGroupEquiv_coefficient (B C : CommAlgCat.{u} R)
    (f : B ⟶ C) (p : WithConv (A →ₐ[R] B)) :
    hopfAffineSchemePointGroupEquiv C (commutativeHopfPointsMap f.hom p) =
      (coordinateRelativeSpec (R := R)).map f.op ≫ hopfAffineSchemePointGroupEquiv B p := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (f.hom.comp p.ofConv).toRingHom) =
    Spec.map (CommRingCat.ofHom f.hom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom p.ofConv.toRingHom)
  exact Spec.map_comp (CommRingCat.ofHom p.ofConv.toRingHom) (CommRingCat.ofHom f.hom.toRingHom)

end
end Dubon2026
