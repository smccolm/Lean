import Dubon2026.SymmetricDualityMatrix

/-! The source parity of the original symmetric-power duality matrix.
Combining this sign with an odd rank-two real-place involution will give
the symmetric conjugate-duality matrix required by DUB-17. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {R : Type*} [CommRing R]

/-- Reversing the original binomial determinant coefficient gives exactly the degree parity. -/
theorem symmetricDualityCoefficient_rev (n : ℕ) (i : Fin (n + 1)) :
    (n.choose i.rev.val : R) * (-1) ^ (n - i.rev.val) =
      (-1) ^ n * ((n.choose i.val : R) * (-1) ^ (n - i.val)) := by
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hr : i.rev.val = n - i.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self hi, Nat.choose_symm hi]
  have hp : (-1 : R) ^ n = (-1) ^ i.val * (-1) ^ (n - i.val) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  have hs : (-1 : R) ^ (n - i.val) * (-1) ^ (n - i.val) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  rw [hp]
  symm
  calc
    _ = (n.choose i.val : R) * (-1) ^ i.val *
        ((-1) ^ (n - i.val) * (-1) ^ (n - i.val)) := by ring
    _ = _ := by rw [hs, mul_one]

/-- The actual degree-n duality matrix is symmetric or alternating with its exact degree sign. -/
theorem symmetricDualityMatrix_transpose (n : ℕ) :
    (symmetricDualityMatrix (R := R) n).transpose = (-1 : R) ^ n • symmetricDualityMatrix n := by
  ext i j
  by_cases h : j = i.rev
  · subst j
    simpa only [Matrix.transpose_apply, Matrix.smul_apply, symmetricDualityMatrix,
      Fin.rev_rev, if_pos rfl, smul_eq_mul] using symmetricDualityCoefficient_rev (R := R) n i
  · have h' : i ≠ j.rev := by
      intro he
      apply h
      rw [he, Fin.rev_rev]
    simp only [Matrix.transpose_apply, Matrix.smul_apply, symmetricDualityMatrix,
      if_neg h, if_neg h', smul_zero]

end
end Dubon2026
