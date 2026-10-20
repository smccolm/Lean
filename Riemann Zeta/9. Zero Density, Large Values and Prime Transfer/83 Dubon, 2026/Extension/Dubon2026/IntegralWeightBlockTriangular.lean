import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Basic

/-! Last-coordinate block factorizations for the original highest-weight line.
The required dependency is DUB-17/18, source potential automorphy, Geraghty's
literal induced coefficients, then uniqueness of their highest-weight line.
Native Schur factorization suffices for the generic open cell; a full Bruhat
decomposition and its additional infrastructure are unnecessary here.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The original matrix with its final coordinate separated from the first coordinates. -/
def integralWeightLastBlock (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin 1) K) (C : Matrix (Fin 1) (Fin n) K)
    (D : Matrix (Fin 1) (Fin 1) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

/-- An upper block matrix with an upper-triangular first block is upper triangular in the original coordinate order. -/
theorem integralWeightLastBlock_upper (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin 1) K) (D : Matrix (Fin 1) (Fin 1) K)
    (hA : A.BlockTriangular id) :
    (integralWeightLastBlock A B 0 D).BlockTriangular id := by
  rw [integralWeightLastBlock, Matrix.blockTriangular_reindex_iff]
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact hA (by simpa using hij)
  · have h : n + j.val < i.val := hij
    omega
  · rfl
  · have h : n + j.val < n + i.val := hij
    omega

/-- A lower block matrix with a lower-triangular first block is lower triangular in the original coordinate order. -/
theorem integralWeightLastBlock_lower (A : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin 1) (Fin n) K) (D : Matrix (Fin 1) (Fin 1) K)
    (hA : A.BlockTriangular OrderDual.toDual) :
    (integralWeightLastBlock A 0 C D).BlockTriangular OrderDual.toDual := by
  rw [integralWeightLastBlock, Matrix.blockTriangular_reindex_iff]
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact hA (by simpa using hij)
  · rfl
  · have h : n + i.val < j.val := hij
    omega
  · have h : n + i.val < n + j.val := hij
    omega

/-- Last-coordinate reindexing preserves the actual product of block matrices. -/
theorem integralWeightLastBlock_mul (A E : Matrix (Fin n) (Fin n) K)
    (B F : Matrix (Fin n) (Fin 1) K) (C G : Matrix (Fin 1) (Fin n) K)
    (D H : Matrix (Fin 1) (Fin 1) K) :
    integralWeightLastBlock A B C D * integralWeightLastBlock E F G H =
      integralWeightLastBlock (A * E + B * G) (A * F + B * H)
        (C * E + D * G) (C * F + D * H) := by
  simp only [integralWeightLastBlock, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

/-- The native Schur factorization transports to the original ordered matrix. -/
theorem integralWeightLastBlock_schur (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin 1) K) (C : Matrix (Fin 1) (Fin n) K)
    (D : Matrix (Fin 1) (Fin 1) K) [Invertible A] :
    integralWeightLastBlock A B C D =
      integralWeightLastBlock 1 0 (C * ⅟A) 1 *
        integralWeightLastBlock A 0 0 (D - C * ⅟A * B) *
          integralWeightLastBlock 1 (⅟A * B) 0 1 := by
  simp only [integralWeightLastBlock, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [← Matrix.fromBlocks_eq_of_invertible₁₁]

end
end Dubon2026
