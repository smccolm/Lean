import Dubon2026.MatrixAdjointCocycles
import Dubon2026.PolarizedSwitch

/-! The full matrix adjoint of CHT Section 2.1. The scalar multiplier cancels
in conjugation, while switching acts by negative transpose. This supplies
the exact coefficient representation for DUB-17's polarized deformation
tangent comparison, without replacing it by the trace-zero adjoint. -/

namespace Dubon2026
open Matrix

variable {ι R : Type} [CommRing R]

/-- The source involution acts on the full matrix algebra by negative transpose. -/
def polarizedAdjointInvolution : Module.End R (Matrix ι ι R) where
  toFun X := -X.transpose
  map_add' X Y := by simp [add_comm]
  map_smul' a X := by simp

/-- Negative transpose is an actual linear involution. -/
theorem polarizedAdjointInvolution_sq :
    (polarizedAdjointInvolution (ι := ι) (R := R)) ^ 2 = 1 := by
  ext X i j
  simp [pow_two, polarizedAdjointInvolution]

/-- The source involution, as a unit of the original linear endomorphism ring. -/
def polarizedAdjointInvolutionUnit : (Module.End R (Matrix ι ι R))ˣ where
  val := polarizedAdjointInvolution
  inv := polarizedAdjointInvolution
  val_inv := by simpa only [pow_two] using polarizedAdjointInvolution_sq (ι := ι) (R := R)
  inv_val := by simpa only [pow_two] using polarizedAdjointInvolution_sq (ι := ι) (R := R)

/-- The linear unit has order dividing two. -/
theorem polarizedAdjointInvolutionUnit_sq :
    (polarizedAdjointInvolutionUnit (ι := ι) (R := R)) ^ 2 = 1 := by
  apply Units.ext
  exact polarizedAdjointInvolution_sq

variable [Fintype ι] [DecidableEq ι]

/-- Multiplying an invertible matrix by a scalar unit does not change its full adjoint action. -/
theorem matrixAdjoint_scalar (u : Rˣ) (g : GeneralLinearGroup ι R) (X : Matrix ι ι R) :
    (GeneralLinearGroup.scalar ι u * g).val * X *
        (GeneralLinearGroup.scalar ι u * g).inv = g.val * X * g.inv := by
  change (Matrix.scalar ι (u : R) * g.val) * X *
    (g.inv * Matrix.scalar ι ((u⁻¹ : Rˣ) : R)) = _
  simp only [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    ← Matrix.smul_eq_mul_diagonal, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp

/-- The literal multiplier-twisted contragredient has the required negative-transpose adjoint. -/
theorem polarizedAdjoint_switch (x : GeneralLinearGroup ι R × Rˣ)
    (X : Matrix ι ι R) :
    (polarizedSwitch x).1.val * X * (polarizedSwitch x).1.inv =
      -((x.1.val * (-X.transpose) * x.1.inv).transpose) := by
  rw [polarizedSwitch, matrixAdjoint_scalar]
  change x.1.inv.transpose * X * x.1.val.transpose = _
  simp only [transpose_mul, transpose_neg, transpose_transpose, mul_neg, neg_mul, neg_neg]
  simp only [mul_assoc]

end Dubon2026
