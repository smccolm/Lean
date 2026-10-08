import Dubon2026.RealAffineLift

/-! # Exact multiplication and normalized coordinates of the original affine matrices -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- Multiplication of the genuine affine matrices has its actual affine coordinate law. -/
theorem realAffineMatrix_mul (x u : ℝ) {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    realAffineMatrix x hy * realAffineMatrix u hv =
      realAffineMatrix (x + y * u) (mul_pos hy hv) := by
  have hy0 := (Real.sqrt_pos.mpr hy).ne'
  have hv0 := (Real.sqrt_pos.mpr hv).ne'
  have hy2 := Real.sq_sqrt hy.le
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [realAffineMatrix, UpperHalfPlane.toSL2R, coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, Real.sqrt_mul hy.le, mul_inv_rev]
  · field_simp [hy0, hv0]
    rw [hy2]
    ring
  · ring

/-- A positive affine matrix decomposes into a fixed original affine matrix and the exact relative coordinates. -/
theorem realAffineMatrix_relative (x x₀ : ℝ) {y y₀ : ℝ} (hy : 0 < y) (hy₀ : 0 < y₀) :
    realAffineMatrix x hy = realAffineMatrix x₀ hy₀ *
      realAffineMatrix ((x - x₀) / y₀) (div_pos hy hy₀) := by
  rw [realAffineMatrix_mul]
  have he : x₀ + y₀ * ((x - x₀) / y₀) = x := by field_simp; ring
  have hy' : y₀ * (y / y₀) = y := by field_simp
  simp only [he, hy']

/-- Positive real half-weight factors multiply according to the actual affine dilation law. -/
theorem realAffineWeight_mul (a : ℝ) {y v : ℝ} (hy : 0 < y) (hv : 0 < v) :
    Real.exp (Real.log (y * v) * a) = Real.exp (Real.log y * a) * Real.exp (Real.log v * a) := by
  rw [Real.log_mul hy.ne' hv.ne', add_mul, Real.exp_add]

end
end Dubon2026
