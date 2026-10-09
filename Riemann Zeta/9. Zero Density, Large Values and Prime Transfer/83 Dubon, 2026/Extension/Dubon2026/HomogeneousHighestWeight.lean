import Dubon2026.HomogeneousDeterminantTwist
import Dubon2026.HomogeneousFiniteSpace

/-! # The actual highest-weight line of the original algebraic GL₂ representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Every original upper-triangular matrix acts on the actual first-coordinate pure power by its first diagonal entry to the homogeneous degree. -/
theorem homogeneousPurePower_upper (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ) (ha : a 1 0 = 0) :
    homogeneousMatrixAction n a (homogeneousPurePower n (0 : Fin 2)) =
      (a 0 0) ^ n • homogeneousPurePower n (0 : Fin 2) := by
  apply Subtype.ext
  change matrixPolynomialAction a (X 0 ^ n) = (a 0 0) ^ n • (X 0 ^ n)
  rw [map_pow, matrixPolynomialAction_X]
  simp only [Fin.sum_univ_two, ha, zero_smul, add_zero, smul_pow]

/-- The genuine determinant twist preserves the original highest-weight line under every actual upper-triangular group element. -/
theorem homogeneousDeterminantTwist_highest_line (m : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (hg : g.val 1 0 = 0) :
    homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g (homogeneousPurePower (2 * m) (0 : Fin 2)) =
      (Matrix.det g.val ^ (-(m : ℤ)) * (g.val 0 0) ^ (2 * m)) •
        homogeneousPurePower (2 * m) (0 : Fin 2) := by
  change Matrix.det g.val ^ (-(m : ℤ)) •
    homogeneousMatrixAction (2 * m) g.val (homogeneousPurePower (2 * m) (0 : Fin 2)) = _
  rw [homogeneousPurePower_upper _ _ hg, smul_smul]

/-- The original diagonal torus element with any two specified nonzero complex entries. -/
def complexDiagonalGL (u v : ℂˣ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![(u : ℂ), (v : ℂ)])
    (by simp [u.ne_zero, v.ne_zero])

/-- The actual torus element retains its two original diagonal entries. -/
theorem complexDiagonalGL_val (u v : ℂˣ) :
    (complexDiagonalGL u v).val = Matrix.diagonal ![(u : ℂ), (v : ℂ)] := rfl

/-- The actual nonzero highest vector of degree 2m and determinant twist det^-m has the exact integral torus weight (m,-m). -/
theorem homogeneousDeterminantTwist_highest_weight (m : ℕ) (u v : ℂˣ) :
    homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (complexDiagonalGL u v)
      (homogeneousPurePower (2 * m) (0 : Fin 2)) =
      ((u : ℂ) ^ m * (v : ℂ) ^ (-(m : ℤ))) • homogeneousPurePower (2 * m) (0 : Fin 2) := by
  rw [homogeneousDeterminantTwist_highest_line m _ (by simp [complexDiagonalGL_val])]
  congr 1
  simp only [complexDiagonalGL_val]
  norm_num [Matrix.det_fin_two, Matrix.diagonal_apply]
  rw [mul_pow]
  have hu : (u : ℂ) ^ m ≠ 0 := pow_ne_zero m u.ne_zero
  rw [show 2 * m = m + m by omega, pow_add]
  field_simp

/-- The actual integral highest weight is dominant, and its rho-shifted entries are distinct with positive difference 2m+1. -/
theorem homogeneousHighestWeight_regular (m : ℕ) :
    -(m : ℤ) ≤ (m : ℤ) ∧ (m : ℤ) + 1 - (-(m : ℤ)) = 2 * m + 1 ∧
      0 < (m : ℤ) + 1 - (-(m : ℤ)) := by omega

end
end Dubon2026
