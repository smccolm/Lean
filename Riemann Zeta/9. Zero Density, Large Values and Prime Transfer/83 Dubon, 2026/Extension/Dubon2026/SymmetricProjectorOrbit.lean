import Dubon2026.FiniteSymmetricMonomialOrbit
import Dubon2026.MatrixConjugationColumnSpan

/-! Literal conjugation of the extremal symmetric-power projector.
Its binomial column is the input to the existing distinct-weight
extraction in DUB-17's regular commuting trace test. -/

namespace Dubon2026
noncomputable section
open Matrix MvPolynomial Module
open scoped BigOperators

variable {K : Type} [Field K]

/-- The upper elementary inverse is the elementary matrix with opposite
parameter, on the original SL2 matrices. -/
theorem ringUpperUnipotent_inv (t : K) :
    (ringUpperUnipotent t)⁻¹ = ringUpperUnipotent (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ringUpperUnipotent, Matrix.adjugate_fin_two]

/-- The original symmetric upper unipotent fixes the zeroth coordinate
functional, including at every inverse parameter. -/
theorem symmetricUpperUnipotent_row_zero (n : ℕ) (t : K) (i : Fin (n + 1)) :
    (homogeneousSymmetricGL n (SpecialLinearGroup.toGL (ringUpperUnipotent t))).val 0 i =
      if i = 0 then 1 else 0 := by
  rw [homogeneousSymmetricGL_val, LinearMap.toMatrix_apply,
    ← homogeneous_eval_zero_one_eq_repr_zero]
  change aeval ![0, 1]
    (homogeneousMatrixAction n (ringUpperUnipotent t).val
      (binaryHomogeneousMonomialBasis n i)).val = _
  rw [homogeneousMatrixAction_apply, binaryHomogeneousMonomialBasis_val]
  by_cases hi : i = 0
  · subst i
    simp [matrixPolynomialAction_X, Fin.sum_univ_two, ringUpperUnipotent]
  · have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
    simp [matrixPolynomialAction_X, Fin.sum_univ_two, ringUpperUnipotent, hi, hn]

/-- Multiplication of the original extremal projector by any symmetric
upper unipotent leaves it unchanged. -/
theorem symmetricProjector_mul_upper (n : ℕ) (t : K) :
    Matrix.single (0 : Fin (n + 1)) 0 1 *
      (homogeneousSymmetricGL n (SpecialLinearGroup.toGL (ringUpperUnipotent t))).val =
        Matrix.single 0 0 1 := by
  ext i j
  by_cases hi : i = 0
  · subst i
    simp [Matrix.mul_apply, Matrix.single, symmetricUpperUnipotent_row_zero, eq_comm]
  · simp [Matrix.mul_apply, Matrix.single, Ne.symm hi]

/-- The literal symmetric conjugate of the extremal projector is its
binomial first-column expansion over the original field. -/
theorem symmetricProjector_upper_conjugate (n : ℕ) :
    let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
    (ψ (ringUpperUnipotent 1)).val * Matrix.single (0 : Fin (n + 1)) 0 1 *
      (ψ (ringUpperUnipotent 1)⁻¹).val =
        ∑ i : Fin (n + 1), (n.choose i.val : K) • Matrix.single i 0 1 := by
  dsimp only [MonoidHom.comp_apply]
  rw [ringUpperUnipotent_inv, mul_assoc, symmetricProjector_mul_upper,
    matrix_mul_single_column_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [homogeneousSymmetricGL_val, LinearMap.toMatrix_apply]
  exact homogeneous_upperUnipotent_basis_zero_repr n i

end
end Dubon2026
