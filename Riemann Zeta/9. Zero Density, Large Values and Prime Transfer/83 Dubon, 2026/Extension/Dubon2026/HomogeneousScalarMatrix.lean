import Dubon2026.HomogeneousFiniteSpace
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! # Exact original central matrix action on homogeneous polynomials -/

namespace Dubon2026

noncomputable section
open MvPolynomial

/-- Scaling every original variable scales each actual monomial by its total degree. -/
theorem homogeneousScaling_monomial {ι : Type*} (c a : ℂ) (d : ι →₀ ℕ) :
    MvPolynomial.aeval (fun i => c • (X i : MvPolynomial ι ℂ)) (monomial d a) =
      c ^ d.degree • monomial d a := by
  classical
  rw [aeval_monomial, Finsupp.prod]
  simp only [smul_pow, Finset.prod_smul, Finset.prod_pow_eq_pow_sum, prod_X_pow_eq_monomial]
  rw [mul_smul_comm, MvPolynomial.algebraMap_eq, C_mul_monomial, mul_one]
  rfl

/-- Scaling the original variables acts on every genuine homogeneous polynomial by the exact degree power. -/
theorem homogeneousScaling_apply {ι : Type*} (c : ℂ) {n : ℕ} {p : MvPolynomial ι ℂ}
    (hp : p.IsHomogeneous n) :
    MvPolynomial.aeval (fun i => c • (X i : MvPolynomial ι ℂ)) p = c ^ n • p := by
  classical
  calc
    _ = ∑ d ∈ p.support, MvPolynomial.aeval (fun i => c • (X i : MvPolynomial ι ℂ))
        (monomial d (p.coeff d)) := by rw [← map_sum, support_sum_monomial_coeff]
    _ = ∑ d ∈ p.support, c ^ n • monomial d (p.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [homogeneousScaling_monomial]
      have he : d.degree = n := by
        rw [Finsupp.degree_eq_weight_one]
        exact hp (mem_support_iff.mp hd)
      rw [he]
    _ = c ^ n • p := by rw [← Finset.smul_sum, support_sum_monomial_coeff]

/-- The genuine scalar matrix has exactly the original degree-power action on the actual homogeneous space. -/
theorem homogeneousMatrixAction_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (c : ℂ) (p : homogeneousSubmodule ι ℂ n) :
    homogeneousMatrixAction n (c • (1 : Matrix ι ι ℂ)) p = c ^ n • p := by
  apply Subtype.ext
  change matrixPolynomialAction (c • (1 : Matrix ι ι ℂ)) p.val = c ^ n • p.val
  have he : matrixPolynomialAction (c • (1 : Matrix ι ι ℂ)) =
      MvPolynomial.aeval (fun i => c • (X i : MvPolynomial ι ℂ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [matrixPolynomialAction_X, Matrix.one_apply, MvPolynomial.aeval_X]
  rw [he]
  exact homogeneousScaling_apply c p.property

end
end Dubon2026
