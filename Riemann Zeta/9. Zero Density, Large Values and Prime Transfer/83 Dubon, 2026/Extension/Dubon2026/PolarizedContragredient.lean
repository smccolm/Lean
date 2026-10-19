import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Basic

/-! The inverse-transpose automorphism used in CHT Section 2.1's polarized
target group. This is the first algebraic dependency of the actual CM
deformation comparison on DUB-17's potential-automorphy route. It constructs
the original matrix operation; no polarized representation is assumed or
claimed to have been realized by this module. -/

namespace Dubon2026
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The literal inverse transpose, as an invertible matrix. -/
def polarizedInverseTranspose (g : GeneralLinearGroup ι R) : GeneralLinearGroup ι R where
  val := g.inv.transpose
  inv := g.val.transpose
  val_inv := by rw [← transpose_mul, g.val_inv, transpose_one]
  inv_val := by rw [← transpose_mul, g.inv_val, transpose_one]

/-- Inverse transpose has order dividing two on the original general linear group. -/
theorem polarizedInverseTranspose_involutive :
    Function.Involutive (polarizedInverseTranspose (R := R) (ι := ι)) := by
  intro g
  apply Units.ext
  exact transpose_transpose g.val

/-- Reversal by inversion cancels reversal by transpose. -/
theorem polarizedInverseTranspose_mul (g h : GeneralLinearGroup ι R) :
    polarizedInverseTranspose (g * h) = polarizedInverseTranspose g * polarizedInverseTranspose h := by
  apply Units.ext
  change (h.inv * g.inv).transpose = g.inv.transpose * h.inv.transpose
  exact transpose_mul _ _

/-- The actual inverse-transpose operation is a group automorphism. -/
def polarizedContragredient : MulAut (GeneralLinearGroup ι R) where
  toFun := polarizedInverseTranspose
  invFun := polarizedInverseTranspose
  left_inv := polarizedInverseTranspose_involutive
  right_inv := polarizedInverseTranspose_involutive
  map_mul' := polarizedInverseTranspose_mul

/-- The automorphism retains its literal inverse-transpose matrix. -/
theorem polarizedContragredient_val (g : GeneralLinearGroup ι R) :
    (polarizedContragredient g).val = g.inv.transpose := rfl

/-- The original scalar character is inverted by the contragredient. -/
theorem polarizedContragredient_scalar (u : Rˣ) :
    polarizedContragredient (GeneralLinearGroup.scalar ι u) =
      GeneralLinearGroup.scalar ι u⁻¹ := by
  apply Units.ext
  ext i j
  simp [polarizedContragredient, polarizedInverseTranspose, GeneralLinearGroup.scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply]

end Dubon2026
