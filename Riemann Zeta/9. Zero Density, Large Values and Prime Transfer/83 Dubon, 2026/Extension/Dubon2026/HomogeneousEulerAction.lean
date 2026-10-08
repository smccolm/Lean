import Dubon2026.HomogeneousPolynomialLie

/-! # The genuine scalar matrix infinitesimal and original Euler degree operator -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original identity-matrix infinitesimal is exactly the actual polynomial Euler derivation. -/
theorem matrixPolynomialDerivation_identity (p : MvPolynomial ι ℂ) :
    matrixPolynomialDerivation (1 : Matrix ι ι ℂ) p = ∑ i, X i * pderiv i p := by
  rw [matrixPolynomialDerivation_eq_sum]
  change Derivation.coeFnAddMonoidHom (∑ i, (∑ j, (1 : Matrix ι ι ℂ) j i • X j) • pderiv i) p = _
  rw [map_sum, Finset.sum_apply]
  simp [Matrix.one_apply, Derivation.smul_apply, smul_eq_mul]

/-- The genuine identity-matrix derivative acts on the original homogeneous degree-n space by the actual scalar n. -/
theorem homogeneousMatrixLieAction_identity (n : ℕ) (p : homogeneousSubmodule ι ℂ n) :
    homogeneousMatrixLieAction n (1 : Matrix ι ι ℂ) p = (n : ℂ) • p := by
  apply Subtype.ext
  change matrixPolynomialDerivation (1 : Matrix ι ι ℂ) p.val = (n : ℂ) • p.val
  rw [matrixPolynomialDerivation_identity, p.property.sum_X_mul_pderiv, Nat.cast_smul_eq_nsmul ℂ]

/-- The genuine scalar-matrix infinitesimal has its exact original homogeneous degree coefficient. -/
theorem homogeneousMatrixLieAction_scalar (n : ℕ) (c : ℂ) (p : homogeneousSubmodule ι ℂ n) :
    homogeneousMatrixLieAction n (c • (1 : Matrix ι ι ℂ)) p = (c * n) • p := by
  rw [map_smul, LinearMap.smul_apply, homogeneousMatrixLieAction_identity, smul_smul]

/-- Removing the actual scalar trace component subtracts its exact degree contribution from the original matrix derivative. -/
theorem homogeneousMatrixLieAction_sub_scalar (n : ℕ) (a : Matrix ι ι ℂ) (c : ℂ)
    (p : homogeneousSubmodule ι ℂ n) :
    homogeneousMatrixLieAction n (a - c • (1 : Matrix ι ι ℂ)) p =
      homogeneousMatrixLieAction n a p - (c * n) • p := by
  rw [map_sub, LinearMap.sub_apply, homogeneousMatrixLieAction_scalar]

end
end Dubon2026
