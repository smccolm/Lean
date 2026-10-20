import Dubon2026.SourceRegularDifferentialEvaluation
import Mathlib.Algebra.Polynomial.Taylor

/-! Actual one-parameter square-zero matrix subgroups for the source right action.
The elementary unipotent directions needed to recover group-stability are
instances of these lines. Only their literal matrix identities are used.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {R A : Type*} [CommRing R] [CommRing A] {n : ℕ}

/-- The actual matrix `1 + t X` for `X² = 0`, with its explicit inverse. -/
def sourceSquareZeroLine (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) (t : R) :
    GeneralLinearGroup (Fin n) R := by
  have hN : (t • X) * (t • X) = 0 := by
    rw [smul_mul_smul_comm, hX, smul_zero]
  exact
    { val := 1 + t • X
      inv := 1 - t • X
      val_inv := by simp only [mul_sub, add_mul, one_mul, mul_one, hN, add_zero,
        add_sub_cancel_right]
      inv_val := by simp only [sub_mul, mul_add, one_mul, mul_one, hN, sub_zero,
        sub_add_cancel] }

/-- The square-zero property is preserved by every original coefficient-ring map. -/
theorem sourceSquareZeroMatrix_map (f : R →+* A)
    (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) :
    X.map f * X.map f = 0 := by
  rw [← Matrix.map_mul, hX, Matrix.map_zero _ (map_zero f)]

/-- The original square-zero matrix line is an actual additive one-parameter subgroup. -/
theorem sourceSquareZeroLine_add (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0)
    (s t : R) :
    sourceSquareZeroLine X hX (s + t) =
      sourceSquareZeroLine X hX s * sourceSquareZeroLine X hX t := by
  apply Units.ext
  change 1 + (s + t) • X = (1 + s • X) * (1 + t • X)
  have h : (s • X) * (t • X) = 0 := by rw [smul_mul_smul_comm, hX, smul_zero]
  simp only [mul_add, add_mul, one_mul, mul_one, h, add_zero, add_smul, add_assoc]

/-- The actual square-zero line commutes with every original coefficient-ring map. -/
theorem sourceSquareZeroLine_map (f : R →+* A)
    (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) (t : R) :
    GeneralLinearGroup.map f (sourceSquareZeroLine X hX t) =
      sourceSquareZeroLine (X.map f) (sourceSquareZeroMatrix_map f X hX) (f t) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases h : i = j <;> simp [sourceSquareZeroLine, h]

/-- At zero the original square-zero line is the identity matrix. -/
theorem sourceSquareZeroLine_zero (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) :
    sourceSquareZeroLine X hX 0 = 1 := by
  apply Units.ext
  simp [sourceSquareZeroLine]

end
end Dubon2026
