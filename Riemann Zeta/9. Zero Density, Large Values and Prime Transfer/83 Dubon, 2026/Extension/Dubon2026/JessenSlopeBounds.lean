import Dubon2026.JessenLeftLimit
import Dubon2026.JessenRightLimit

/-! # Global derivative and secant bounds for the actual Jessen function -/

namespace Dubon2026

open Set Filter
open scoped Topology

/-- Both asymptotic slopes bound every right derivative. -/
theorem jessen_rightDeriv_bounds {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (x : ℝ) :
    -Real.log (lastIndex a N) ≤ derivWithin (jessenFunction a N) (Ioi x) x ∧
      derivWithin (jessenFunction a N) (Ioi x) x ≤ 0 := by
  have hconv := convexOn_jessenFunction hN (ha.trans_ne one_ne_zero)
  have hm := monotone_convex_rightDeriv hconv
  constructor
  · apply le_of_tendsto (tendsto_jessen_derivatives_atBot hN (ha.trans_ne one_ne_zero)).2
    filter_upwards [eventually_le_atBot x] with y hy
    exact hm hy
  · apply ge_of_tendsto (tendsto_jessen_derivatives_atTop hN ha).2
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hm hy

/-- Every actual secant lies between the terminal-frequency slope and zero. -/
theorem jessen_slope_bounds {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {x y : ℝ} (hxy : x < y) :
    -Real.log (lastIndex a N) ≤ slope (jessenFunction a N) x y ∧
      slope (jessenFunction a N) x y ≤ 0 := by
  have hconv := convexOn_jessenFunction hN (ha.trans_ne one_ne_zero)
  exact ⟨(jessen_rightDeriv_bounds hN ha x).1.trans
    (hconv.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ y) hxy),
    (hconv.slope_le_leftDeriv_of_mem_interior (mem_univ x) (by simp) hxy).trans
      ((hconv.leftDeriv_le_rightDeriv_of_mem_interior (by simp)).trans
        (jessen_rightDeriv_bounds hN ha y).2)⟩

theorem antitone_jessenFunction {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) : Antitone (jessenFunction a N) := by
  intro x y hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  have hh := (jessen_slope_bounds hN ha hxy).2
  rw [slope_def_field] at hh
  exact sub_nonpos.mp (by linarith [(div_le_iff₀ (sub_pos.mpr hxy)).mp hh])

/-- The terminal frequency gives a global Lipschitz bound by log N. -/
theorem jessen_sub_le_log_mul {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {x y : ℝ} (hxy : x ≤ y) :
    jessenFunction a N x - jessenFunction a N y ≤ Real.log N * (y - x) := by
  rcases hxy.eq_or_lt with rfl | hxy
  · simp
  have hm : (0 : ℝ) < lastIndex a N := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_lastIndex hN (ha.trans_ne one_ne_zero)))
  have hlog := Real.log_le_log hm (show (lastIndex a N : ℝ) ≤ N by exact_mod_cast lastIndex_le a N)
  have hs := (jessen_slope_bounds hN ha hxy).1
  rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at hs
  have hh := mul_le_mul_of_nonneg_right hlog (sub_nonneg.mpr hxy.le)
  nlinarith

end Dubon2026
