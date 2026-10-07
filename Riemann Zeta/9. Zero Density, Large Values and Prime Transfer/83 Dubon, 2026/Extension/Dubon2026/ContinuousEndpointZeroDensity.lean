import Dubon2026.RegularApproximation
import Dubon2026.RegularZeroDensity
import Dubon2026.ZeroCountInterval

/-! # Zero density at all differentiable Jessen endpoints, including lines containing zeros -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_zeroDensity_differentiable_endpoints {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u dl du : ℝ} (hlu : l < u)
    (hdl : HasDerivAt (jessenFunction a N) dl l)
    (hdu : HasDerivAt (jessenFunction a N) du u) :
    Tendsto (fun T => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop (𝓝 ((du - dl) / (2 * Real.pi))) := by
  let D := fun x => derivWithin (jessenFunction a N) (Ioi x) x
  have heL : D l = dl := hdl.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi l)
  have heU : D u = du := hdu.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi u)
  rw [← heL, ← heU]
  have hf := convexOn_jessenFunction hN (ha.trans_ne one_ne_zero)
  have hcL := continuousAt_convex_rightDeriv_of_hasDerivAt hf hdl
  have hcU := continuousAt_convex_rightDeriv_of_hasDerivAt hf hdu
  let q := (D u - D l) / (2 * Real.pi)
  have hq : q * (2 * Real.pi) = D u - D l := by
    dsimp [q]
    field_simp
  apply tendsto_order.mpr
  constructor
  · intro b hb
    change b < q at hb
    let ε := (q - b) * Real.pi / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hr : 0 < (u - l) / 3 := by positivity
    obtain ⟨l', hl', hDl, hnL, hdL⟩ := exists_regular_abscissa_right_close
      hN (ha.trans_ne one_ne_zero) l hcL hr hε
    obtain ⟨u', hu', hDu, hnU, hdU⟩ := exists_regular_abscissa_left_close
      hN (ha.trans_ne one_ne_zero) u hcU hr hε
    have hl'u' : l' ≤ u' := by linarith [hl'.2, hu'.1]
    have hinner : b < (D u' - D l') / (2 * Real.pi) := by
      apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have h1 := (abs_lt.mp hDl).2
      have h2 := (abs_lt.mp hDu).1
      change D l' - D l < ε at h1
      change -ε < D u' - D u at h2
      have hgap := mul_pos (sub_pos.mpr hb) Real.pi_pos
      dsimp [ε] at h1 h2
      nlinarith
    have hlim := tendsto_zeroDensity_regular_endpoints hN ha hl'u' hnL hnU hdL hdU
    filter_upwards [(tendsto_order.mp hlim).1 b hinner, eventually_gt_atTop (0 : ℝ)] with T hT hpos
    apply hT.trans_le
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast verticalZeroCount_mono_interval hN (ha.trans_ne one_ne_zero) hl'.1.le hu'.2.le T
  · intro b hb
    change q < b at hb
    let ε := (b - q) * Real.pi / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    obtain ⟨l', hl', hDl, hnL, hdL⟩ := exists_regular_abscissa_left_close
      hN (ha.trans_ne one_ne_zero) l hcL (show (0 : ℝ) < 1 by norm_num) hε
    obtain ⟨u', hu', hDu, hnU, hdU⟩ := exists_regular_abscissa_right_close
      hN (ha.trans_ne one_ne_zero) u hcU (show (0 : ℝ) < 1 by norm_num) hε
    have hl'u' : l' ≤ u' := by linarith [hl'.2, hu'.1]
    have houter : (D u' - D l') / (2 * Real.pi) < b := by
      apply (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
      have h1 := (abs_lt.mp hDl).1
      have h2 := (abs_lt.mp hDu).2
      change -ε < D l' - D l at h1
      change D u' - D u < ε at h2
      have hgap := mul_pos (sub_pos.mpr hb) Real.pi_pos
      dsimp [ε] at h1 h2
      nlinarith
    have hlim := tendsto_zeroDensity_regular_endpoints hN ha hl'u' hnL hnU hdL hdU
    filter_upwards [(tendsto_order.mp hlim).2 b houter, eventually_gt_atTop (0 : ℝ)] with T hT hpos
    apply lt_of_le_of_lt ?_ hT
    apply div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast verticalZeroCount_mono_interval hN (ha.trans_ne one_ne_zero) hl'.2.le hu'.1.le T

end Dubon2026
