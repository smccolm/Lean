import Dubon2026.MatrixPolynomialCurveEvaluation
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! # Genuine complex derivatives of the actual polynomial matrix orbit -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Evaluating the actual matrix orbit at any original coordinate point has derivative equal to the original matrix derivation. -/
theorem matrixPolynomialOrbit_hasDerivAt (a : Matrix ι ι ℂ) (p : MvPolynomial ι ℂ) (x : ι → ℂ) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval x (matrixPolynomialAction (1 + t • a) p))
      (MvPolynomial.eval x (matrixPolynomialDerivation a p)) 0 := by
  let q : Polynomial ℂ := (matrixPolynomialCurve a p).map (MvPolynomial.eval x)
  have hq (t : ℂ) : q.eval t = MvPolynomial.eval x (matrixPolynomialAction (1 + t • a) p) := by
    have he := Polynomial.eval_map_apply (p := matrixPolynomialCurve a p) (MvPolynomial.eval x) (C t)
    simpa only [MvPolynomial.eval_C, matrixPolynomialCurve_eval] using he
  have hd : q.derivative.eval 0 = MvPolynomial.eval x (matrixPolynomialDerivation a p) := by
    change ((matrixPolynomialCurve a p).map (MvPolynomial.eval x)).derivative.eval 0 = _
    rw [Polynomial.derivative_map]
    have he := Polynomial.eval_map_apply (p := (matrixPolynomialCurve a p).derivative)
      (MvPolynomial.eval x) 0
    simpa only [map_zero, matrixPolynomialCurve_tangent] using he
  have he := q.hasDerivAt 0
  rw [show (fun t => q.eval t) = (fun t => MvPolynomial.eval x (matrixPolynomialAction (1 + t • a) p))
    from funext hq, hd] at he
  exact he

end
end Dubon2026
