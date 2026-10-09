import Mathlib.LinearAlgebra.Matrix.Ideal
import Mathlib.RingTheory.Ideal.Operations

/-! # Actual coefficient-ideal products in the original matrix ring -/

namespace Dubon2026

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Matrix multiplication sends the original coefficient ideals to their actual ideal product. -/
theorem matrixIdeal_mul_mem (I J : Ideal R) {X Y : Matrix ι ι R}
    (hX : X ∈ I.matrix ι) (hY : Y ∈ J.matrix ι) :
    X * Y ∈ (I * J).matrix ι := by
  intro i j
  rw [Matrix.mul_apply]
  exact (I * J).sum_mem (fun k _ => Ideal.mul_mem_mul (hX i k) (hY k j))

/-- Every actual matrix power has coefficients in the corresponding original ideal power. -/
theorem matrixIdeal_pow_mem (I : Ideal R) {X : Matrix ι ι R}
    (hX : X ∈ I.matrix ι) (n : ℕ) : X ^ n ∈ (I ^ n).matrix ι := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact matrixIdeal_mul_mem (I ^ n) I ih hX

/-- Multiplication on the right retains membership in the literal coefficient matrix ideal. -/
theorem matrixIdeal_mul_right_mem (I : Ideal R) {X : Matrix ι ι R}
    (hX : X ∈ I.matrix ι) (Y : Matrix ι ι R) : X * Y ∈ I.matrix ι := by
  intro i j
  rw [Matrix.mul_apply]
  exact I.sum_mem (fun k _ => I.mul_mem_right (Y k j) (hX i k))

/-- The original scalar natural-number matrix lies in the coefficient matrix ideal when its scalar coefficient does. -/
theorem matrixIdeal_natCast_mem (I : Ideal R) (p : ℕ) (hp : (p : R) ∈ I) :
    (p : Matrix ι ι R) ∈ I.matrix ι := by
  intro i j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.natCast_apply, if_pos rfl] using hp
  · simp [Matrix.natCast_apply, hij]

end Dubon2026
