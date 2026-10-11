import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # The actual finite-free norm polynomial along a line and its trace derivative -/

namespace Dubon2026
noncomputable section

open Polynomial
open scoped Matrix

variable {R S ι : Type} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R S) (x : S)

/-- The determinant polynomial of actual multiplication by `1 + T x`
in the original finite free algebra and its displayed basis. -/
def finiteFreeNormLinePolynomial : R[X] :=
  Matrix.det (1 + (X : R[X]) • (Algebra.leftMulMatrix b x).map C)

/-- Evaluation gives the genuine original algebra norm of `1 + t x`.
The polynomial is not an abstract surrogate for the norm. -/
theorem finiteFreeNormLinePolynomial_eval (t : R) :
    (finiteFreeNormLinePolynomial b x).eval t = Algebra.norm R (1 + t • x) := by
  rw [Algebra.norm_eq_matrix_det b, map_add, map_one, map_smul]
  change (Polynomial.evalRingHom t)
    (Matrix.det (1 + (X : R[X]) • (Algebra.leftMulMatrix b x).map C)) = _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp only [eval_one, eval_zero] <;> ring

/-- The first derivative of the original norm line at the identity is
the actual algebra trace of the original direction element. -/
theorem finiteFreeNormLinePolynomial_derivative_zero :
    (finiteFreeNormLinePolynomial b x).derivative.eval 0 = Algebra.trace R S x := by
  rw [finiteFreeNormLinePolynomial, Matrix.derivative_det_one_add_X_smul,
    Algebra.trace_eq_matrix_trace b]

include b in
omit [DecidableEq ι] in
/-- In the actual finite free algebra, the norm is a unit exactly when
the original element is a unit. Invertibility of its original multiplication
map is detected by its determinant. -/
theorem finiteFreeNorm_isUnit_iff : IsUnit (Algebra.norm R x) ↔ IsUnit x := by
  letI : Module.Finite R S := Module.Finite.of_basis b
  letI : Module.Free R S := Module.Free.of_basis b
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det, Algebra.lmul_isUnit_iff]

end
end Dubon2026
