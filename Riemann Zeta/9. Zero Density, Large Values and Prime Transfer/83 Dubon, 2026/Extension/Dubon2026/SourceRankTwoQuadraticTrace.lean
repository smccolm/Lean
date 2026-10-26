import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! DUB-17/18 -> primitive Frobenius trace and characteristic polynomial.
Native Cayley-Hamilton and the two-dimensional characteristic polynomial
identify the trace from the separately proved determinant and quadratic
identity. Invertibility is retained from the actual Galois representation. -/
namespace Dubon2026
noncomputable section
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem rank_two_cayley_hamilton (A : Matrix (Fin 2) (Fin 2) K) :
    A * A + A.det • 1 = A.trace • A := by
  have h := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two] at h
  simpa only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, pow_two,
    sub_add_eq_add_sub, sub_eq_zero] using h

theorem rank_two_trace_of_determinant_quadratic
    (A : GeneralLinearGroup (Fin 2) K) (a d : K)
    (hd : A.val.det = d)
    (hq : A.val * A.val + d • 1 = a • A.val) : A.val.trace = a := by
  have hc := rank_two_cayley_hamilton A.val
  rw [hd, hq] at hc
  have hi := congrArg (fun M => M * A.inv) hc
  simp only [smul_mul_assoc, A.val_inv] at hi
  have he := congrArg (fun M => M 0 0) hi
  simpa using he.symm

theorem rank_two_charpoly_of_determinant_quadratic
    (A : GeneralLinearGroup (Fin 2) K) (a d : K)
    (hd : A.val.det = d)
    (hq : A.val * A.val + d • 1 = a • A.val) :
    A.val.charpoly = X ^ 2 - C a * X + C d := by
  rw [Matrix.charpoly_fin_two, hd,
    rank_two_trace_of_determinant_quadratic A a d hd hq]

end
end Dubon2026
