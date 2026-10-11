import Dubon2026.FiniteFreeHopfPoints
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-! # The actual representable presheaf of commutative Hopf-coordinate groups -/

namespace Dubon2026
noncomputable section
open CategoryTheory Opposite WithConv

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A]

/-- Original cocommutativity gives the genuine commutative convolution group for every original commutative algebra of point values. -/
local instance coordinatePresheafPointGroup (B : CommAlgCat.{u} R) :
    CommGroup (WithConv (A →ₐ[R] B)) :=
  { commutativeHopfPointsGroup with mul_comm := mul_comm }

/-- The actual original Hopf coordinates define a presheaf of commutative groups on the opposite category of original commutative algebras. Its maps are genuine composition on the original point values. -/
def hopfCoordinateCommutativeGroupPresheaf :
    ((CommAlgCat.{u} R)ᵒᵖ)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj B := CommGrpCat.of (WithConv (A →ₐ[R] B.unop.unop))
  map f := CommGrpCat.ofHom (commutativeHopfPointsMap (A := A) f.unop.unop.hom)
  map_id B := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro p
    apply WithConv.ext
    ext a
    rfl
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro p
    apply WithConv.ext
    ext a
    rfl

/-- The presheaf is represented by precisely the original coordinate algebra, through the literal original algebra homomorphisms. This constructs the representation rather than assuming representability. -/
def hopfCoordinateCommutativeGroupPresheafRepresentable :
    (hopfCoordinateCommutativeGroupPresheaf (R := R) (A := A) ⋙ forget CommGrpCat).RepresentableBy
      (op (CommAlgCat.of R A)) where
  homEquiv := {
    toFun := fun f => toConv f.unop.hom
    invFun := fun p => (CommAlgCat.ofHom p.ofConv).op
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  homEquiv_comp _ _ := rfl

/-- The actual representation bijection evaluates the original coordinate map on the same original coordinate. -/
theorem hopfCoordinateCommutativeGroupPresheaf_representable_apply
    (B : (CommAlgCat.{u} R)ᵒᵖ) (f : B ⟶ op (CommAlgCat.of R A)) (a : A) :
    ((hopfCoordinateCommutativeGroupPresheafRepresentable (R := R) (A := A)).homEquiv f :
      WithConv (A →ₐ[R] B.unop)).ofConv a =
      f.unop.hom a := by
  rfl

/-- The original opposite algebra category has its genuine categorical products, obtained from the original algebra coproducts. -/
local instance coordinatePresheafCartesian : CartesianMonoidalCategory ((CommAlgCat.{u} R)ᵒᵖ) :=
  CartesianMonoidalCategory.ofHasFiniteProducts

/-- Use the actual symmetry of the chosen categorical products. -/
local instance coordinatePresheafBraided : BraidedCategory ((CommAlgCat.{u} R)ᵒᵖ) :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- The exact original coordinate object is a genuine commutative group object, by the proved original point-group presheaf and its constructed representation. -/
@[implicit_reducible]
def hopfCoordinateCommutativeGroupObject : CommGrpObj (op (CommAlgCat.of R A)) :=
  CommGrpObj.ofRepresentableBy _ (hopfCoordinateCommutativeGroupPresheaf (R := R) (A := A))
    hopfCoordinateCommutativeGroupPresheafRepresentable

/-- The original cocommutative Hopf algebra supplies a genuine commutative group object on its same original opposite coordinate object. -/
theorem hopfCoordinateCommutativeGroupObject_exists :
    Nonempty (CommGrpObj (op (CommAlgCat.of R A))) := by
  exact ⟨hopfCoordinateCommutativeGroupObject⟩

end
end Dubon2026
