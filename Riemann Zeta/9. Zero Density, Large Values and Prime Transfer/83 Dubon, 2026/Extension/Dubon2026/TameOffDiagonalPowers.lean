import Dubon2026.MatrixIdealPowerProducts
import Mathlib.Tactic.NoncommRing

/-! # Off-diagonal ideal-power improvement for tame inertia

The rank-two argument in anthropics/fermats-last-theorem,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Matrix_apply_eq_zero_of_diagonal_mul_eq_pow_mul_diagonal_of_sub_one_mem.lean,
is extended here to the arbitrary ranks needed by Dubon Theorem 2.6.
Apache-2.0; retained license: ../../Dependencies/AnthropicFLTReuse/LICENSE.
The original matrix-ideal multiplication results are reused.
-/

namespace Dubon2026
open Matrix

variable {A ι : Type} [CommRing A] [Fintype ι] [DecidableEq ι]

/-- Powers of a matrix congruent to the identity retain the original coefficient
ideal congruence. -/
theorem matrixIdeal_pow_sub_one_mem (I : Ideal A) (N : Matrix ι ι A)
    (hN : N - 1 ∈ I.matrix ι) (k : ℕ) : N ^ k - 1 ∈ I.matrix ι := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : N ^ (k + 1) - 1 = (N ^ k - 1) * N + (N - 1) := by
      rw [pow_succ]
      noncomm_ring
    rw [he]
    exact (I.matrix ι).add_mem (matrixIdeal_mul_right_mem I ih N) hN

/-- Multiplying two matrices whose coefficients lie in an ideal improves each
off-diagonal coefficient by one ideal power when their off-diagonal entries
already lie in the specified power. -/
theorem matrixIdeal_offDiagonal_mul_mem (I : Ideal A) (n : ℕ)
    (X Y : Matrix ι ι A) (hX : X ∈ I.matrix ι) (hY : Y ∈ I.matrix ι)
    (hXn : ∀ i j, i ≠ j → X i j ∈ I ^ n)
    (hYn : ∀ i j, i ≠ j → Y i j ∈ I ^ n)
    (i j : ι) (hij : i ≠ j) : (X * Y) i j ∈ I ^ (n + 1) := by
  classical
  rw [mul_apply]
  apply (I ^ (n + 1)).sum_mem
  intro k _
  by_cases hik : i = k
  · subst k
    rw [pow_succ']
    exact Ideal.mul_mem_mul (hX i i) (hYn i j hij)
  · rw [pow_succ]
    exact Ideal.mul_mem_mul (hXn i k hik) (hY k j)

/-- The off-diagonal part of an actual matrix power is its linear term modulo
the next coefficient-ideal power. -/
theorem matrixIdeal_offDiagonal_pow_linear (I : Ideal A) (n : ℕ)
    (N : Matrix ι ι A) (hN : N - 1 ∈ I.matrix ι)
    (hNn : ∀ i j, i ≠ j → N i j ∈ I ^ n) (k : ℕ) :
    ∀ i j, i ≠ j → (N ^ k) i j - (k : A) * N i j ∈ I ^ (n + 1) := by
  classical
  induction k with
  | zero => intro i j hij; simp [hij]
  | succ k ih =>
    have hXn : ∀ i j, i ≠ j → (N ^ k - 1) i j ∈ I ^ n := by
      intro i j hij
      have hp : (N ^ k) i j ∈ I ^ n := by
        have he : (N ^ k) i j = ((N ^ k) i j - (k : A) * N i j) +
            (k : A) * N i j := by ring
        rw [he]
        exact (I ^ n).add_mem (Ideal.pow_le_pow_right (Nat.le_succ n) (ih i j hij))
          ((I ^ n).mul_mem_left _ (hNn i j hij))
      simpa [Matrix.sub_apply, hij] using hp
    have hYn : ∀ i j, i ≠ j → (N - 1) i j ∈ I ^ n := by
      intro i j hij
      simpa [Matrix.sub_apply, hij] using hNn i j hij
    intro i j hij
    have hp := matrixIdeal_offDiagonal_mul_mem I n (N ^ k - 1) (N - 1)
      (matrixIdeal_pow_sub_one_mem I N hN k) hN hXn hYn i j hij
    have he : N ^ (k + 1) = (N ^ k - 1) * (N - 1) + N ^ k + N - 1 := by
      rw [pow_succ]
      noncomm_ring
    have heij := congrArg (fun M : Matrix ι ι A => M i j) he
    simp only [add_apply, sub_apply, one_apply_ne hij, sub_zero] at heij
    have hd : (N ^ (k + 1)) i j - ((k + 1 : ℕ) : A) * N i j =
        ((N ^ k - 1) * (N - 1)) i j + ((N ^ k) i j - (k : A) * N i j) := by
      rw [heij]
      push_cast
      ring
    rw [hd]
    exact (I ^ (n + 1)).add_mem hp (ih i j hij)

end Dubon2026
