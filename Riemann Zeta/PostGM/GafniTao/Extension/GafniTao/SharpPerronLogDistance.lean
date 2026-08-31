import GafniTao.SharpPerronHalfPoint

/-!
# Logarithmic distance versus additive distance

These are the exact elementary inequalities used to turn the Perron
denominator `|log(x/n)|` into a reciprocal distance from the cutoff.
-/

namespace GafniTao

theorem sub_div_le_log_div_of_pos_of_lt
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    (x - y) / x ≤ Real.log (x / y) := by
  have hx : 0 < x := hy.trans hyx
  have hq : 0 < x / y := div_pos hx hy
  have h := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div, one_sub_div hx.ne'] at h
  exact h

theorem sub_div_le_neg_log_div_of_pos_of_lt
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (y - x) / y ≤ -Real.log (x / y) := by
  have hy : 0 < y := hx.trans hxy
  have h := sub_div_le_log_div_of_pos_of_lt hx hxy
  rw [Real.log_div hy.ne' hx.ne'] at h
  rw [Real.log_div hx.ne' hy.ne']
  linarith

theorem one_div_log_div_le_div_sub_of_pos_of_lt
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    1 / Real.log (x / y) ≤ x / (x - y) := by
  have hx : 0 < x := hy.trans hyx
  have hlog : 0 < Real.log (x / y) := Real.log_pos ((one_lt_div hy).2 hyx)
  have hsub : 0 < x - y := sub_pos.mpr hyx
  rw [div_le_div_iff₀ hlog hsub]
  have h := sub_div_le_log_div_of_pos_of_lt hy hyx
  rw [div_le_iff₀ hx] at h
  simpa [mul_comm] using h

theorem one_div_neg_log_div_le_div_sub_of_pos_of_lt
    {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    1 / (-Real.log (x / y)) ≤ y / (y - x) := by
  have hy : 0 < y := hx.trans hxy
  have hlog : 0 < -Real.log (x / y) := by
    have : x / y < 1 := (div_lt_one hy).2 hxy
    exact neg_pos.mpr (Real.log_neg (div_pos hx hy) this)
  have hsub : 0 < y - x := sub_pos.mpr hxy
  rw [div_le_div_iff₀ hlog hsub]
  have h := sub_div_le_neg_log_div_of_pos_of_lt hx hxy
  rw [div_le_iff₀ hy] at h
  simpa [mul_comm] using h

end GafniTao
