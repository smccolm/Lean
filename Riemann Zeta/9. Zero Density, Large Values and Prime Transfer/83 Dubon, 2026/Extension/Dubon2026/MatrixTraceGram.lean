import Dubon2026.FullMatrixTracePairing
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Unit determinant of the actual trace Gram matrix in any original full-matrix basis -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing R]

/-- The actual Gram matrix of the original matrix trace pairing in a genuine basis of the entire matrix algebra. -/
def matrixTraceGram (b : Basis κ R (Matrix ι ι R)) : Matrix κ κ R :=
  fun i j => Matrix.trace (b i * b j)

/-- The original trace Gram matrix has an actual left inverse, obtained by expressing the genuine trace-dual matrices in the same original basis. -/
theorem matrixTraceGram_has_left_inverse (b : Basis κ R (Matrix ι ι R)) :
    ∃ T : Matrix κ κ R, T * matrixTraceGram b = 1 := by
  let X : κ → Matrix ι ι R := fun i => fullMatrixTraceDuality.symm (b.coord i)
  let T : Matrix κ κ R := fun i j => b.repr (X i) j
  refine ⟨T, ?_⟩
  ext i k
  have hs := congrArg (fun Z : Matrix ι ι R => Matrix.trace (Z * b k)) (b.sum_repr (X i))
  simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    smul_eq_mul] at hs
  change (∑ j, b.repr (X i) j * Matrix.trace (b j * b k)) = (1 : Matrix κ κ R) i k
  rw [hs]
  have hx : fullMatrixTracePairing (X i) = b.coord i :=
    fullMatrixTraceDuality.apply_symm_apply (b.coord i)
  have hv := DFunLike.congr_fun hx (b k)
  change Matrix.trace (X i * b k) = b.coord i (b k) at hv
  rw [hv]
  simp only [Basis.coord_apply, Basis.repr_self_apply, Matrix.one_apply, eq_comm]

/-- The determinant of the actual original trace Gram matrix is a unit in the original coefficient ring. -/
theorem matrixTraceGram_det_isUnit (b : Basis κ R (Matrix ι ι R)) :
    IsUnit (matrixTraceGram b).det := by
  obtain ⟨T, hT⟩ := matrixTraceGram_has_left_inverse b
  letI := Matrix.detInvertibleOfLeftInverse (matrixTraceGram b) T hT
  exact isUnit_of_invertible _

end
end Dubon2026
