import Dubon2026.GeneralLinearBorelCharacter
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-! Original upper-Borel row elimination at a singular matrix.
The nonzero original diagonal cofactor constructs a determinant-one
upper-triangular matrix that kills the original first row. This is the
linear algebra used at the generic singular point in the exact integral
induced numerator-divisibility proof.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The original adjugate row, normalized by its original first diagonal cofactor, replaces the first row of the identity. -/
def singularUpperRowMatrix (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K).updateRow 0
    (fun j => (A.adjugate 0 0)⁻¹ * A.adjugate 0 j)

/-- The actual normalized adjugate-row matrix is upper triangular. -/
theorem singularUpperRowMatrix_upper (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (singularUpperRowMatrix A).BlockTriangular id := by
  intro i j hij
  have hi : i ≠ 0 := by
    intro h
    subst i
    exact (not_lt_of_ge (Fin.zero_le j)) hij
  have hij' : i ≠ j := ne_of_gt hij
  simp [singularUpperRowMatrix, Matrix.updateRow_ne hi, hij']

/-- Every diagonal entry of the normalized original row matrix is one when the original cofactor is nonzero. -/
theorem singularUpperRowMatrix_diagonal (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA : A.adjugate 0 0 ≠ 0) (i : Fin (n + 1)) : singularUpperRowMatrix A i i = 1 := by
  by_cases hi : i = 0
  · subst i
    simp [singularUpperRowMatrix, hA]
  · simp [singularUpperRowMatrix, Matrix.updateRow_ne hi]

/-- The actual upper row operation has determinant one. -/
theorem singularUpperRowMatrix_det (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hA : A.adjugate 0 0 ≠ 0) : (singularUpperRowMatrix A).det = 1 := by
  rw [Matrix.det_of_upperTriangular (singularUpperRowMatrix_upper A)]
  simp only [singularUpperRowMatrix_diagonal A hA, Finset.prod_const_one]

/-- The original normalized adjugate row kills the first row of the same singular matrix. -/
theorem singularUpperRowMatrix_mul_firstRow (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hdet : A.det = 0) (j : Fin (n + 1)) : (singularUpperRowMatrix A * A) 0 j = 0 := by
  simp only [Matrix.mul_apply, singularUpperRowMatrix, Matrix.updateRow_self]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Matrix.mul_apply, Matrix.adjugate_mul, hdet,
    zero_smul, Matrix.zero_apply, mul_zero]

/-- The original cofactor constructs an actual source upper-Borel element with all diagonal units one that kills the original singular matrix's first row. -/
theorem singularMatrix_exists_upperBorel_firstRow_zero
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hdet : A.det = 0) (hA : A.adjugate 0 0 ≠ 0) :
    ∃ b : generalLinearBorel K (n + 1),
      (∀ i, generalLinearBorelDiagonalUnit b i = 1) ∧
        ∀ j, (b.val.val * A) 0 j = 0 := by
  let g := GeneralLinearGroup.mk'' (singularUpperRowMatrix A)
    (by rw [singularUpperRowMatrix_det A hA]; exact isUnit_one)
  let b : generalLinearBorel K (n + 1) := ⟨g, singularUpperRowMatrix_upper A⟩
  refine ⟨b, ?_, singularUpperRowMatrix_mul_firstRow A hdet⟩
  intro i
  apply Units.ext
  exact singularUpperRowMatrix_diagonal A hA i

end
end Dubon2026
