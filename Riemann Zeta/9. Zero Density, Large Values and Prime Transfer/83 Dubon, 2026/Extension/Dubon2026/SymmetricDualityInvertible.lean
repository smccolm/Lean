import Dubon2026.SymmetricDualityMatrix
import Dubon2026.FiniteSymmetricIrreducible

/-! Invertibility of the actual binomial duality matrix. The existing
factorial-to-binomial nonvanishing theorem discharges the scalar factors;
Mathlib's diagonal and permutation results supply matrix invertibility.
This makes DUB-17's symmetric-power duality an actual GL-valued input. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {K : Type*} [Field K]

/-- The actual binomial antidiagonal is the original diagonal matrix with its columns reversed. -/
theorem symmetricDualityMatrix_reversed_diagonal (n : ℕ) :
    symmetricDualityMatrix (R := K) n =
      (Matrix.diagonal (fun i : Fin (n + 1) => (n.choose i.val : K) * (-1) ^ (n - i.val))).submatrix
        (Equiv.refl _) Fin.revPerm := by
  ext i j
  simp only [symmetricDualityMatrix, Matrix.submatrix_apply, Equiv.refl_apply,
    Fin.revPerm_apply, Matrix.diagonal_apply]
  congr 1
  exact propext (eq_comm.trans Fin.rev_eq_iff)

/-- Existing factorial nonvanishing makes every original duality coefficient a unit. -/
theorem symmetricDualityMatrix_isUnit (n : ℕ) (hn : (n.factorial : K) ≠ 0) :
    IsUnit (symmetricDualityMatrix (R := K) n) := by
  rw [symmetricDualityMatrix_reversed_diagonal, Matrix.isUnit_submatrix_equiv, Matrix.isUnit_diagonal]
  exact Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr
    (mul_ne_zero (choose_cast_ne_zero_of_factorial n hn i) (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)))

/-- The genuine original binomial duality matrix, as an invertible matrix. -/
def symmetricDualityGL (n : ℕ) (hn : (n.factorial : K) ≠ 0) : GeneralLinearGroup (Fin (n + 1)) K :=
  (symmetricDualityMatrix_isUnit n hn).unit

/-- The invertible duality matrix retains every original binomial coefficient. -/
theorem symmetricDualityGL_val (n : ℕ) (hn : (n.factorial : K) ≠ 0) :
    (symmetricDualityGL n hn).val = symmetricDualityMatrix n :=
  (symmetricDualityMatrix_isUnit n hn).unit_spec

end
end Dubon2026
