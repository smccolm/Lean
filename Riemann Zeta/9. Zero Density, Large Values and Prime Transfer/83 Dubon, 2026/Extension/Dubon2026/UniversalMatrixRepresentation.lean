import Dubon2026.RepresentationCoordinateRelations

/-! # The genuine universal matrix representation over its actual coordinate algebra -/

namespace Dubon2026

noncomputable section
open Matrix

variable (G ι R : Type*) [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The original coordinate matrices as an actual matrix-valued group homomorphism. -/
def universalCoordinateMatrixHom : G →* Matrix ι ι (RepresentationCoordinateAlgebra G ι R) where
  toFun := representationCoordinateMatrix G ι R
  map_one' := representationCoordinateMatrix_one G ι R
  map_mul' := representationCoordinateMatrix_mul G ι R

/-- The original universal matrices are invertible because they form a genuine representation of the original group. -/
def universalMatrixRepresentation :
    G →* GeneralLinearGroup ι (RepresentationCoordinateAlgebra G ι R) :=
  (universalCoordinateMatrixHom G ι R).toHomUnits

/-- The genuine universal representation retains the literal original coordinate class in each matrix entry. -/
theorem universalMatrixRepresentation_entry (g : G) (i j : ι) :
    (universalMatrixRepresentation G ι R g).val i j =
      Ideal.Quotient.mk (representationCoordinateIdeal G ι R)
        (MvPolynomial.X (g, i, j)) := rfl

/-- The actual original coordinate matrix is invertible in its original coordinate algebra. -/
theorem representationCoordinateMatrix_isUnit (g : G) :
    IsUnit (representationCoordinateMatrix G ι R g) :=
  (universalMatrixRepresentation G ι R g).isUnit

end
end Dubon2026
