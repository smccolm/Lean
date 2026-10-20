import Dubon2026.HomogeneousMatrixPolynomial
import Dubon2026.HomogeneousMatrixColumns
import Dubon2026.BinaryTensorCovariance

/-! The faithful polynomial encoding transforms by the literal original
symmetric-power matrices on both sides. This supplies the exact matrix
consumer of determinant covariance for DUB-17's polarization. -/

namespace Dubon2026
open MvPolynomial Matrix Module
noncomputable section

variable {R : Type*} [CommRing R]

/-- Simultaneous substitution is precisely congruence by the original homogeneous symmetric-power matrix. -/
theorem homogeneousMatrixPolynomial_covariance (n : ℕ) (g : GeneralLinearGroup (Fin 2) R)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    matrixPolynomialAction (Matrix.fromBlocks g.val 0 0 g.val) (homogeneousMatrixPolynomial n A) =
      homogeneousMatrixPolynomial n
        ((homogeneousSymmetricGL n g).val * A * (homogeneousSymmetricGL n g).val.transpose) := by
  rw [Matrix.mul_assoc]
  simp only [homogeneousMatrixPolynomial, map_sum, map_smul, binaryTensorPolynomial_covariance,
    homogeneousSymmetricGL_column_polynomial, binaryTensorPolynomial_sum_smul,
    Finset.smul_sum, smul_smul, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_smul]
  let S := (homogeneousSymmetricGL n g).val
  let b := fun i j : Fin (n + 1) => binaryTensorPolynomial
    (binaryHomogeneousMonomialBasis (R := R) n i).val (binaryHomogeneousMonomialBasis n j).val
  change (∑ i, ∑ j, ∑ k, ∑ l, (A i j * (S k i * S l j)) • b k l) =
    ∑ k, ∑ l, ∑ i, ∑ j, (S k i * (A i j * S l j)) • b k l
  calc
    _ = ∑ i, ∑ k, ∑ j, ∑ l, (A i j * (S k i * S l j)) • b k l := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l, (A i j * (S k i * S l j)) • b k l := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ l, ∑ j, (A i j * (S k i * S l j)) • b k l := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ∑ i, ∑ j, (A i j * (S k i * S l j)) • b k l := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = _ := by simp only [mul_left_comm]

end
end Dubon2026
