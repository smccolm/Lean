import Dubon2026.HomogeneousMatrixPolynomialCovariance
import Dubon2026.FiniteSymmetricMonomialOrbit
import Mathlib.Data.Nat.Choose.Sum

/-! The literal binomial antidiagonal matrix from the nth power of the
two-vector determinant. Its covariance is the original symmetric-power
duality identity needed by the CM polarization in DUB-17. -/

namespace Dubon2026
open MvPolynomial Matrix Module
noncomputable section

variable {R : Type*} [CommRing R]

/-- The original binomial coefficients and determinant signs form the symmetric-power duality matrix. -/
def symmetricDualityMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  fun i j => if j = i.rev then (n.choose i.val : R) * (-1) ^ (n - i.val) else 0

/-- The matrix encoding is the actual determinant polynomial to the nth power. -/
theorem homogeneousMatrixPolynomial_symmetricDuality (n : ℕ) :
    homogeneousMatrixPolynomial n (symmetricDualityMatrix (R := R) n) =
      binaryDeterminantPolynomial ^ n := by
  simp only [homogeneousMatrixPolynomial, symmetricDualityMatrix, ite_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [binaryDeterminantPolynomial, sub_eq_add_neg, add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [binaryTensorPolynomial, binaryHomogeneousMonomialBasis_val, binaryHomogeneousMonomialBasis_val]
  have hr : i.rev.val = n - i.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)]
  have hneg : -(X (Sum.inl 1) * X (Sum.inr 0) : MvPolynomial (Fin 2 ⊕ Fin 2) R) =
      (-1) * (X (Sum.inl 1) * X (Sum.inr 0)) := neg_eq_neg_one_mul _
  rw [hneg]
  simp only [map_mul, map_pow, rename_X, smul_eq_C_mul, map_natCast, map_neg, map_one, mul_pow]
  ring

/-- Original matrix scaling is retained by the faithful homogeneous polynomial encoding. -/
theorem homogeneousMatrixPolynomial_smul (n : ℕ) (c : R)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    homogeneousMatrixPolynomial n (c • A) = c • homogeneousMatrixPolynomial n A := by
  simp only [homogeneousMatrixPolynomial, Matrix.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

/-- The literal original symmetric-power matrix preserves its duality matrix with multiplier det(g)^n. -/
theorem symmetricDualityMatrix_covariance (n : ℕ) (g : GeneralLinearGroup (Fin 2) R) :
    (homogeneousSymmetricGL n g).val * symmetricDualityMatrix n *
        (homogeneousSymmetricGL n g).val.transpose = g.val.det ^ n • symmetricDualityMatrix n := by
  apply homogeneousMatrixPolynomial_injective n
  rw [← homogeneousMatrixPolynomial_covariance, homogeneousMatrixPolynomial_smul,
    homogeneousMatrixPolynomial_symmetricDuality, binaryDeterminantPolynomial_pow_covariance,
    smul_eq_C_mul]

end
end Dubon2026
