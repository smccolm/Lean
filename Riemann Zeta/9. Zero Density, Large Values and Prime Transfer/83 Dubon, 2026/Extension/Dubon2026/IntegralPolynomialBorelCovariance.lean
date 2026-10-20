import Dubon2026.GeneralLinearIntegralInduction
import Dubon2026.MatrixPolynomialDensity

/-! Extending the original induced polynomial covariance to singular matrices.
The source gives covariance on GL_n over every coefficient algebra. The
actual polynomial identity follows over any infinite coefficient field,
using the adapted proved density lemma. The same original polynomial
therefore satisfies covariance at the generic singular matrix.
-/

namespace Dubon2026
noncomputable section
open Matrix MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The literal polynomial substitution for left multiplication by the original matrix. -/
def polynomialMatrixLeftSubstitute (B : Matrix (Fin n) (Fin n) A) :
    MvPolynomial (Fin n × Fin n) A →ₐ[A] MvPolynomial (Fin n × Fin n) A :=
  MvPolynomial.aeval (fun ij : Fin n × Fin n =>
    ∑ k : Fin n, MvPolynomial.C (B ij.1 k) * MvPolynomial.X (k, ij.2))

/-- Evaluating the original left-matrix polynomial substitution equals evaluation at the original matrix product. -/
theorem polynomialMatrixLeftSubstitute_eval
    (B M : Matrix (Fin n) (Fin n) A) (P : MvPolynomial (Fin n × Fin n) A) :
    MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)
      (polynomialMatrixLeftSubstitute B P) =
    MvPolynomial.eval (fun ij : Fin n × Fin n => (B * M) ij.1 ij.2) P := by
  change MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2)
    (MvPolynomial.aeval _ P) = _
  rw [MvPolynomial.comp_aeval_apply]
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, Matrix.mul_apply]
  rfl

universe u
variable {R : Type u} [CommRing R]

/-- The exact source covariance of an original polynomial induced function holds at every matrix over an infinite coefficient field, including singular matrices. -/
theorem generalLinearIntegralPolynomial_borel_matrix {n : ℕ}
    (lam : Fin n → ℤ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularPolynomialMap R n P ∈
      generalLinearIntegralInducedSubmodule R n lam)
    (K : Type u) [Field K] [Infinite K] [Algebra R K]
    (b : generalLinearBorel K n) (M : Matrix (Fin n) (Fin n) K) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n => (b.val.val * M) ij.1 ij.2) P =
      (generalLinearBorelWeight lam b : K) *
        MvPolynomial.aeval (fun ij : Fin n × Fin n => M ij.1 ij.2) P := by
  let Q := MvPolynomial.map (algebraMap R K) P
  have he : polynomialMatrixLeftSubstitute b.val.val Q =
      MvPolynomial.C (generalLinearBorelWeight lam b : K) * Q := by
    apply MvPolynomial.eq_of_eval_eq_on_gl
    intro g
    have h := hP K g b
    rw [generalLinearRegularEval_polynomial, generalLinearRegularEval_polynomial] at h
    simpa only [polynomialMatrixLeftSubstitute_eval, map_mul, MvPolynomial.eval_C,
      Q, MvPolynomial.eval_map, ← MvPolynomial.aeval_def] using h
  have h := congrArg (MvPolynomial.eval (fun ij : Fin n × Fin n => M ij.1 ij.2)) he
  simpa only [polynomialMatrixLeftSubstitute_eval, map_mul, MvPolynomial.eval_C,
    Q, MvPolynomial.eval_map, ← MvPolynomial.aeval_def] using h

end
end Dubon2026
