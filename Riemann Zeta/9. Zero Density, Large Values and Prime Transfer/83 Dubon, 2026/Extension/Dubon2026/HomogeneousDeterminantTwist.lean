import Dubon2026.HomogeneousScalarMatrix

/-! # The genuine determinant twist of the original homogeneous GL₂ representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Twist the genuine original homogeneous GL₂ action by an actual integral determinant character. -/
def homogeneousDeterminantTwist (n : ℕ) (m : ℤ) :
    Representation ℂ (Matrix.GeneralLinearGroup (Fin 2) ℂ)
      (homogeneousSubmodule (Fin 2) ℂ n) where
  toFun g := ((Matrix.GeneralLinearGroup.det g : ℂ) ^ m) • homogeneousGLRepresentation n g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, mul_zpow, smul_mul_smul_comm]

/-- The genuine determinant twist keeps its literal determinant factor and original matrix substitution. -/
theorem homogeneousDeterminantTwist_apply (n : ℕ) (m : ℤ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (p : homogeneousSubmodule (Fin 2) ℂ n) :
    homogeneousDeterminantTwist n m g p =
      ((Matrix.GeneralLinearGroup.det g : ℂ) ^ m) • homogeneousGLRepresentation n g p := rfl

/-- The original homogeneous general linear action has the exact degree-power central character. -/
theorem homogeneousGLRepresentation_scalar (n : ℕ) (u : ℂˣ)
    (p : homogeneousSubmodule (Fin 2) ℂ n) :
    homogeneousGLRepresentation n (Matrix.GeneralLinearGroup.scalar (Fin 2) u) p = (u : ℂ) ^ n • p := by
  have he : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u) : Matrix (Fin 2) (Fin 2) ℂ) =
      (u : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  change homogeneousMatrixAction n ((Matrix.GeneralLinearGroup.scalar (Fin 2) u) : Matrix (Fin 2) (Fin 2) ℂ) p = _
  rw [he, homogeneousMatrixAction_scalar]

/-- For even homogeneous degree 2m, the actual determinant twist det^-m has genuinely trivial central action. -/
theorem homogeneousDeterminantTwist_trivial_center (m : ℕ) (u : ℂˣ)
    (p : homogeneousSubmodule (Fin 2) ℂ (2 * m)) :
    homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) (Matrix.GeneralLinearGroup.scalar (Fin 2) u) p = p := by
  rw [homogeneousDeterminantTwist_apply, homogeneousGLRepresentation_scalar,
    Matrix.GeneralLinearGroup.det_scalar]
  simp only [Fintype.card_fin, Units.val_pow_eq_pow_val, zpow_neg, zpow_natCast,
    smul_smul, pow_mul]
  rw [inv_mul_cancel₀ (pow_ne_zero m (pow_ne_zero 2 u.ne_zero)), one_smul]

end
end Dubon2026
