import Dubon2026.MatrixPolynomialTangent

/-! # The original matrix polynomial curve evaluates to the actual group substitution -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original formal matrix curve specializes to the literal substitution by I+tA for every complex t. -/
theorem matrixPolynomialCurve_eval (a : Matrix ι ι ℂ) (t : ℂ) (p : MvPolynomial ι ℂ) :
    Polynomial.eval (C t) (matrixPolynomialCurve a p) = matrixPolynomialAction (1 + t • a) p := by
  let ev : Polynomial (MvPolynomial ι ℂ) →ₐ[ℂ] MvPolynomial ι ℂ :=
    Polynomial.eval₂AlgHom (AlgHom.id ℂ (MvPolynomial ι ℂ)) (C t) (fun _ => Commute.all _ _)
  have he : ev.comp (matrixPolynomialCurve a) = matrixPolynomialAction (1 + t • a) := by
    apply MvPolynomial.algHom_ext
    intro i
    change Polynomial.eval (C t) (matrixPolynomialCurve a (X i)) = _
    rw [matrixPolynomialCurve_X, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    simp [matrixPolynomialAction_X, Matrix.add_apply, Matrix.one_apply, add_smul,
      Finset.sum_add_distrib, C_mul', Finset.smul_sum, smul_smul]
  exact AlgHom.congr_fun he p

end
end Dubon2026
