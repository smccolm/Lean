import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix

/-! # Polynomial and continuous characteristic coefficients of the original matrices -/

namespace Dubon2026

noncomputable section

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The literal characteristic coefficient of the matrix of independent entry variables. -/
def matrixCharacteristicCoefficientPolynomial (k : ℕ) : MvPolynomial (ι × ι) R :=
  (Matrix.charpoly (fun i j : ι => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) R))).coeff k

/-- Evaluation of the original universal entry variables gives exactly the original matrix characteristic coefficient. -/
theorem matrixCharacteristicCoefficientPolynomial_eval (k : ℕ) (A : Matrix ι ι R) :
    MvPolynomial.eval (fun ij : ι × ι => A ij.1 ij.2)
        (matrixCharacteristicCoefficientPolynomial k) = A.charpoly.coeff k := by
  let φ := MvPolynomial.eval (fun ij : ι × ι => A ij.1 ij.2)
  have he := Matrix.charpoly_map
    (fun i j : ι => (MvPolynomial.X (i, j) : MvPolynomial (ι × ι) R)) φ
  have hm : Matrix.map (fun i j : ι => (MvPolynomial.X (i, j) :
      MvPolynomial (ι × ι) R)) φ = A := by
    ext i j
    exact MvPolynomial.eval_X (i, j)
  rw [hm] at he
  have hc := congrArg (fun p : Polynomial R => p.coeff k) he
  simpa only [Polynomial.coeff_map] using hc.symm

/-- Every characteristic coefficient of the actual matrix is continuous over its original topological coefficient ring. -/
theorem matrixCharacteristicCoefficient_continuous [TopologicalSpace R] [IsTopologicalRing R]
    (k : ℕ) : Continuous (fun A : Matrix ι ι R => A.charpoly.coeff k) := by
  simp_rw [← matrixCharacteristicCoefficientPolynomial_eval]
  apply (MvPolynomial.continuous_eval _).comp
  apply continuous_pi
  intro ij
  exact (continuous_apply ij.2).comp (continuous_apply ij.1)

end
end Dubon2026
