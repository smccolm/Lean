import Dubon2026.MatrixIdealPowerProducts
import Dubon2026.IdempotentNewtonStep
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Actual matrix idempotent-improvement iterates and their coefficient-ideal errors -/

namespace Dubon2026
open Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual successive cubic improvements of the original matrix. -/
def matrixIdempotentNewtonSequence (X : Matrix ι ι R) : ℕ → Matrix ι ι R
  | 0 => X
  | n + 1 => idempotentNewtonStep (matrixIdempotentNewtonSequence X n)

/-- Each genuine cubic improvement doubles the original entrywise coefficient-ideal order of the idempotency error. -/
theorem matrixIdempotentNewtonSequence_error (I : Ideal R) (X : Matrix ι ι R)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ I) (n : ℕ) :
    ∀ i j, ((matrixIdempotentNewtonSequence X n) ^ 2 -
      matrixIdempotentNewtonSequence X n) i j ∈ I ^ (2 ^ n) := by
  induction n with
  | zero => simpa only [matrixIdempotentNewtonSequence, pow_zero, pow_one] using hX
  | succ n hn =>
    let E := (matrixIdempotentNewtonSequence X n) ^ 2 - matrixIdempotentNewtonSequence X n
    have hE : ∀ i j, (E ^ 2) i j ∈ I ^ (2 ^ n + 2 ^ n) := by
      simpa only [pow_two, pow_add] using
        matrixIdeal_mul_mem (I ^ (2 ^ n)) (I ^ (2 ^ n)) (X := E) (Y := E) hn hn
    intro i j
    change ((idempotentNewtonStep (matrixIdempotentNewtonSequence X n)) ^ 2 -
      idempotentNewtonStep (matrixIdempotentNewtonSequence X n)) i j ∈ I ^ (2 ^ (n + 1))
    rw [idempotentNewtonStep_error]
    have hexp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ, Nat.mul_two]
    rw [hexp]
    exact matrixIdeal_mul_right_mem _ hE (4 * E - 3) i j

/-- Each actual successive matrix difference belongs entrywise to the same rapidly increasing coefficient-ideal power as the current idempotency error. -/
theorem matrixIdempotentNewtonSequence_sub (I : Ideal R) (X : Matrix ι ι R)
    (hX : ∀ i j, (X ^ 2 - X) i j ∈ I) (n : ℕ) (i j : ι) :
    (matrixIdempotentNewtonSequence X (n + 1) - matrixIdempotentNewtonSequence X n) i j ∈
      I ^ (2 ^ n) := by
  change (idempotentNewtonStep (matrixIdempotentNewtonSequence X n) -
    matrixIdempotentNewtonSequence X n) i j ∈ _
  rw [idempotentNewtonStep_sub]
  have h := matrixIdeal_mul_mem ⊤ (I ^ (2 ^ n))
    (X := 1 - 2 * matrixIdempotentNewtonSequence X n)
    (Y := (matrixIdempotentNewtonSequence X n) ^ 2 - matrixIdempotentNewtonSequence X n)
    (by intro i j; trivial) (matrixIdempotentNewtonSequence_error I X hX n)
  simpa only [Ideal.top_mul] using h i j

/-- Every actual improvement stays in the same original coefficient matrix subalgebra as the original seed. -/
theorem matrixIdempotentNewtonSequence_mem {O : Type*} [CommRing O]
    [Algebra O (Matrix ι ι R)] (S : Subalgebra O (Matrix ι ι R))
    (X : Matrix ι ι R) (hX : X ∈ S) (n : ℕ) : matrixIdempotentNewtonSequence X n ∈ S := by
  induction n with
  | zero => exact hX
  | succ n hn =>
    change 3 * (matrixIdempotentNewtonSequence X n) ^ 2 -
      2 * (matrixIdempotentNewtonSequence X n) ^ 3 ∈ S
    exact S.sub_mem (S.mul_mem (S.natCast_mem 3) (S.pow_mem hn 2))
      (S.mul_mem (S.natCast_mem 2) (S.pow_mem hn 3))

end Dubon2026
