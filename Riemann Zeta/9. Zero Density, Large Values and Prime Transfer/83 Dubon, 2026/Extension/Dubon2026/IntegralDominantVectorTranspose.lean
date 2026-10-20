import Dubon2026.IntegralDominantInducedVector

/-! The literal dominant induced vector is unchanged by matrix transpose.
This gives its exact right opposite-Borel character from its already
proved left source covariance. After the longest permutation this is
the required original highest-weight vector; irreducibility and the
complete highest-weight identification are separate obligations.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

/-- Transpose of an actual invertible matrix, with the transposed original inverse. -/
def integralWeightTranspose (g : GeneralLinearGroup (Fin n) R) :
    GeneralLinearGroup (Fin n) R where
  val := g.val.transpose
  inv := g.inv.transpose
  val_inv := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]

/-- Transposing the original matrix twice returns that same matrix. -/
theorem integralWeightTranspose_involutive (g : GeneralLinearGroup (Fin n) R) :
    integralWeightTranspose (integralWeightTranspose g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose g.val

/-- The determinant unit of the actual transposed matrix is unchanged. -/
theorem integralWeightTranspose_det (g : GeneralLinearGroup (Fin n) R) :
    GeneralLinearGroup.det (integralWeightTranspose g) = GeneralLinearGroup.det g := by
  apply Units.ext
  exact Matrix.det_transpose g.val

/-- Transpose reverses the original invertible matrix product. -/
theorem integralWeightTranspose_mul (g h : GeneralLinearGroup (Fin n) R) :
    integralWeightTranspose (g * h) = integralWeightTranspose h * integralWeightTranspose g := by
  apply Units.ext
  exact Matrix.transpose_mul g.val h.val

/-- The literal fundamental regular vector has the same value on the original matrix and its transpose. -/
theorem integralInducedFundamentalVector_eval_transpose
    {A : Type u} [CommRing A] [Algebra R A]
    (g : GeneralLinearGroup (Fin n) A) (k : Fin n) :
    generalLinearRegularEval (integralWeightTranspose g) (integralInducedFundamentalVector R n k) =
      generalLinearRegularEval g (integralInducedFundamentalVector R n k) := by
  simp only [integralInducedFundamentalVector, generalLinearRegularEval_polynomial,
    integralInducedTrailingMinorPolynomial_eval]
  change ((g.val.submatrix
    (fun i : {i : Fin n // k ≤ i} => i.val) (fun i : {i : Fin n // k ≤ i} => i.val)).transpose).det = _
  exact Matrix.det_transpose _

/-- The actual dominant source vector is invariant under transposing its evaluated matrix, over every original coefficient algebra. -/
theorem integralDominantInducedVector_eval_transpose
    {A : Type u} [CommRing A] [Algebra R A] (lam : Fin (n + 1) → ℤ)
    (g : GeneralLinearGroup (Fin (n + 1)) A) :
    generalLinearRegularEval (integralWeightTranspose g) (integralDominantInducedVector R lam) =
      generalLinearRegularEval g (integralDominantInducedVector R lam) := by
  simp only [integralDominantInducedVector, map_mul, map_prod, map_pow,
    generalLinearRegularEval_determinant_zpow, integralWeightTranspose_det,
    integralInducedFundamentalVector_eval_transpose]

/-- The original dominant vector has the exact opposite-Borel right character, derived from its literal source covariance. -/
theorem integralDominantInducedVector_right_transpose_borel
    {A : Type u} [CommRing A] [Algebra R A] (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam)
    (g : GeneralLinearGroup (Fin (n + 1)) A) (b : generalLinearBorel A (n + 1)) :
    generalLinearRegularEval (g * integralWeightTranspose b.val) (integralDominantInducedVector R lam) =
      (generalLinearBorelWeight lam b : A) *
        generalLinearRegularEval g (integralDominantInducedVector R lam) := by
  rw [← integralDominantInducedVector_eval_transpose lam (g * integralWeightTranspose b.val),
    integralWeightTranspose_mul, integralWeightTranspose_involutive]
  rw [integralDominantInducedVector_mem R lam hlam A (integralWeightTranspose g) b,
    integralDominantInducedVector_eval_transpose]

end
end Dubon2026
