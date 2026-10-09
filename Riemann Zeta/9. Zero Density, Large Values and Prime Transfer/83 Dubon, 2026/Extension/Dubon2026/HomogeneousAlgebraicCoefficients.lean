import Dubon2026.HomogeneousPolynomialCoefficients
import Dubon2026.HomogeneousDeterminantTwist

/-! # Actual regular matrix coefficients of the original algebraic determinant twist -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Every genuine matrix coefficient of the original determinant-twisted representation is an actual polynomial divided by a power of the original nonzero determinant. -/
theorem homogeneousDeterminantTwist_regular_coefficient (m : ℕ)
    (p : homogeneousSubmodule (Fin 2) ℂ (2 * m))
    (L : homogeneousSubmodule (Fin 2) ℂ (2 * m) →ₗ[ℂ] ℂ) :
    ∃ q : MvPolynomial (Fin 2 × Fin 2) ℂ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℂ,
      L (homogeneousDeterminantTwist (2 * m) (-(m : ℤ)) g p) =
        MvPolynomial.eval (fun ij => g.val ij.1 ij.2) q / (Matrix.det g.val) ^ m := by
  obtain ⟨q, hq⟩ := homogeneousMatrixCoefficient_polynomial (2 * m) p L
  refine ⟨q, fun g => ?_⟩
  change L ((Matrix.det g.val) ^ (-(m : ℤ)) • homogeneousMatrixAction (2 * m) g.val p) = _
  rw [map_smul, hq, smul_eq_mul, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_comm]

end
end Dubon2026
