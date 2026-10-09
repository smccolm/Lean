import Dubon2026.MatrixPolynomialAction

/-! # Genuine polynomial matrix coefficients of the original substitution representation -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- Substitute the actual universal matrix, with independent polynomial variables for its original entries. -/
def universalMatrixPolynomialAction :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι (MvPolynomial (ι × ι) R) :=
  aeval (fun i => ∑ j, C (X (j, i)) * X j)

/-- Evaluation of the universal original entry variables gives precisely the genuine original matrix substitution. -/
theorem universalMatrixPolynomialAction_eval (a : Matrix ι ι R) (p : MvPolynomial ι R) :
    MvPolynomial.map (MvPolynomial.eval (fun ij : ι × ι => a ij.1 ij.2))
      (universalMatrixPolynomialAction p) = matrixPolynomialAction a p := by
  have he : (MvPolynomial.mapAlgHom (MvPolynomial.aeval (fun ij : ι × ι => a ij.1 ij.2))).comp
      universalMatrixPolynomialAction = matrixPolynomialAction a := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [universalMatrixPolynomialAction, matrixPolynomialAction_X, smul_eq_C_mul]
  exact congrArg (fun F : MvPolynomial ι R →ₐ[R] MvPolynomial ι R => F p) he

/-- Each literal original output coefficient is the evaluation of one actual polynomial in the original matrix entries. -/
def matrixCoefficientPolynomial (p : MvPolynomial ι R) (d : ι →₀ ℕ) : MvPolynomial (ι × ι) R :=
  MvPolynomial.coeff d (universalMatrixPolynomialAction p)

/-- The genuine universal coefficient polynomial retains exactly the original matrix coefficient at every matrix. -/
theorem matrixCoefficientPolynomial_eval (p : MvPolynomial ι R) (d : ι →₀ ℕ) (a : Matrix ι ι R) :
    MvPolynomial.eval (fun ij : ι × ι => a ij.1 ij.2) (matrixCoefficientPolynomial p d) =
      MvPolynomial.coeff d (matrixPolynomialAction a p) := by
  rw [← universalMatrixPolynomialAction_eval a p, MvPolynomial.coeff_map]
  rfl

end
end Dubon2026
