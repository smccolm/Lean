import Dubon2026.HopfCoordinateCommutativeGroupPresheaf
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # The actual affine commutative group scheme of Hopf coordinates -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits

universe u
variable {R : Type u} [CommRing R]

/-- The original relative affine spectrum functor, constructed from the actual algebra-under equivalence and the actual spectrum functor on original ring maps. -/
def coordinateRelativeSpec :
    (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
  (commAlgCatEquivUnder (CommRingCat.of R)).op.functor ⋙
    (Over.opEquivOpUnder (CommRingCat.of R)).inverse ⋙ Over.post Scheme.Spec

/-- Original relative spectrum preserves finite products because the algebra-under functors are equivalences and the spectrum right adjoint preserves finite limits, also in the over category. -/
local instance relativeSpecPreservesProducts : PreservesFiniteProducts (coordinateRelativeSpec (R := R)) := by
  unfold coordinateRelativeSpec
  haveI : PreservesFiniteProducts (commAlgCatEquivUnder (CommRingCat.of R)).op.functor := by
    infer_instance
  haveI : PreservesFiniteProducts (Over.opEquivOpUnder (CommRingCat.of R)).inverse := by
    infer_instance
  haveI : PreservesFiniteLimits Scheme.Spec.{u} := by infer_instance
  haveI : PreservesFiniteProducts (Over.post Scheme.Spec (X := op (CommRingCat.of R))) := by
    infer_instance
  exact comp_preservesFiniteProducts
    (commAlgCatEquivUnder (CommRingCat.of R)).op.functor
    ((Over.opEquivOpUnder (CommRingCat.of R)).inverse ⋙ Over.post Scheme.Spec)

/-- Use the original finite products of opposite coordinate algebras. -/
local instance affineGroupCoordinateCartesian : CartesianMonoidalCategory ((CommAlgCat.{u} R)ᵒᵖ) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

/-- Use the original symmetry on products of opposite coordinate algebras. -/
local instance affineGroupCoordinateBraided : BraidedCategory ((CommAlgCat.{u} R)ᵒᵖ) :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- Relative schemes use the genuine scheme fiber products over the original base. -/
local instance affineGroupSchemeCartesian : CartesianMonoidalCategory (Over (Spec (CommRingCat.of R))) :=
  Over.cartesianMonoidalCategory _

/-- Use the original symmetry on scheme fiber products over the original base. -/
local instance affineGroupSchemeBraided : BraidedCategory (Over (Spec (CommRingCat.of R))) :=
  Over.braidedCategory _

/-- Original relative spectrum is braided for its actual product-preserving structure. -/
local instance affineGroupRelativeSpecBraided : (coordinateRelativeSpec (R := R)).Braided :=
  Functor.Braided.ofChosenFiniteProducts _

variable {A : Type u} [CommRing A] [HopfAlgebra R A] [Coalgebra.IsCocomm R A]

/-- The original commutative Hopf algebra defines a genuine commutative group object in schemes over its original base spectrum. The group structure is transported from the constructed representable original point presheaf. -/
def hopfCoordinateAffineGroupScheme : CommGrp (Over (Spec (CommRingCat.of R))) := by
  letI : CommGrpObj (op (CommAlgCat.of R A)) := hopfCoordinateCommutativeGroupObject
  exact (coordinateRelativeSpec (R := R)).mapCommGrp.obj { X := op (CommAlgCat.of R A) }

/-- The constructed group scheme has exactly the original affine spectrum and original structure map. -/
theorem hopfCoordinateAffineGroupScheme_structure :
    (hopfCoordinateAffineGroupScheme (R := R) (A := A)).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rfl

/-- Finiteness of the same original coordinate module proves finiteness of the actual group-scheme structure morphism. -/
theorem hopfCoordinateAffineGroupScheme_finite [Module.Finite R A] :
    IsFinite (hopfCoordinateAffineGroupScheme (R := R) (A := A)).X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- Flatness of the same original coordinate module proves flatness of the actual group-scheme structure morphism. -/
theorem hopfCoordinateAffineGroupScheme_flat [Module.Flat R A] :
    AlgebraicGeometry.Flat (hopfCoordinateAffineGroupScheme (R := R) (A := A)).X.hom := by
  change AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (algebraMap R A)))
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end
end Dubon2026
