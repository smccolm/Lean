import Mathlib.Data.Matrix.Basis

/-! # The genuine column description of a residual matrix-unit left ideal -/

namespace Dubon2026
open Matrix

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

/-- An original matrix fixed on the right by a diagonal matrix unit is exactly the sum of its original selected-column entries times the corresponding matrix units. -/
theorem matrix_eq_sum_single_column (X : Matrix ι ι K) (i₀ : ι)
    (hX : X * Matrix.single i₀ i₀ 1 = X) :
    X = ∑ i, X i i₀ • Matrix.single i i₀ 1 := by
  ext i j
  have hx := congrArg (fun Y : Matrix ι ι K => Y i j) hX
  change (X * Matrix.single i₀ i₀ (1 : K) : Matrix ι ι K) i j = X i j at hx
  by_cases hj : j = i₀
  · subst j
    simp [Matrix.sum_apply, Matrix.single, smul_eq_mul]
  · have hz : X i j = 0 := by
      rw [Matrix.mul_single_apply_of_ne 1 i₀ i₀ i j hj X] at hx
      exact hx.symm
    rw [hz]
    simp [Matrix.sum_apply, Matrix.single, Ne.symm hj, smul_eq_mul]

end Dubon2026
