import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! DUB-17/18 -> residual Frobenius association. Extract the exact trace
and determinant from the transported two-dimensional characteristic
polynomial, including in the actual positive-characteristic residue field. -/
namespace Dubon2026
noncomputable section
open Matrix Polynomial
variable {R : Type*} [CommRing R] [Nontrivial R]

theorem rank_two_trace_det_of_charpoly (A : Matrix (Fin 2) (Fin 2) R) (a d : R)
    (h : A.charpoly = X ^ 2 - C a * X + C d) : A.trace = a ∧ A.det = d := by
  constructor
  · have h1 := congrArg (fun P : R[X] => P.coeff 1) h
    simpa [Matrix.charpoly_fin_two] using h1
  · have h0 := congrArg (fun P : R[X] => P.coeff 0) h
    simpa [Matrix.charpoly_fin_two] using h0

end
end Dubon2026
