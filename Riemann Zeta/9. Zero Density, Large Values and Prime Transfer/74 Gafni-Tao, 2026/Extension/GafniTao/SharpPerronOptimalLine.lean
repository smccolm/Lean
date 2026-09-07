import GafniTao.SharpPerronAdditiveBounds

/-!
# The optimized right Perron line

For a physical evaluation point `y > 1`, the standard sharp-Perron choice is
`c = 1 + 1 / log y`.  This file records the exact identities and monotonicity
facts needed later; in particular, the factor `y^c` is exactly `e*y`, rather
than merely being hidden in big-O notation.
-/

namespace GafniTao

/-- The real part of the optimized Perron line at scale `y`. -/
noncomputable def sharpPerronAbscissa (y : ℝ) : ℝ :=
  1 + 1 / Real.log y

theorem one_lt_sharpPerronAbscissa {y : ℝ} (hy : 1 < y) :
    1 < sharpPerronAbscissa y := by
  unfold sharpPerronAbscissa
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hinv : 0 < 1 / Real.log y := one_div_pos.mpr hlog
  linarith

theorem sharpPerronAbscissa_pos {y : ℝ} (hy : 1 < y) :
    0 < sharpPerronAbscissa y :=
  (by linarith [one_lt_sharpPerronAbscissa hy])

theorem sharpPerronAbscissa_le_logTwoConstant {y : ℝ} (hy : 2 ≤ y) :
    sharpPerronAbscissa y ≤ 1 + 1 / Real.log 2 := by
  unfold sharpPerronAbscissa
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log y := Real.log_le_log (by positivity) hy
  gcongr

/-- Exact cancellation behind the optimized Perron factor. -/
theorem rpow_sharpPerronAbscissa {y : ℝ} (hy : 1 < y) :
    y ^ sharpPerronAbscissa y = Real.exp 1 * y := by
  have hy0 : 0 < y := by positivity
  have hlog : Real.log y ≠ 0 := (Real.log_pos hy).ne'
  rw [Real.rpow_def_of_pos hy0]
  unfold sharpPerronAbscissa
  have hmul : Real.log y * (1 + 1 / Real.log y) = Real.log y + 1 := by
    field_simp
  rw [hmul, Real.exp_add, Real.exp_log hy0]
  ring

theorem sharpPerronAbscissa_sub_one {y : ℝ} (hy : 1 < y) :
    (sharpPerronAbscissa y - 1)⁻¹ = Real.log y := by
  unfold sharpPerronAbscissa
  have hlog : Real.log y ≠ 0 := (Real.log_pos hy).ne'
  field_simp
  ring

end GafniTao
