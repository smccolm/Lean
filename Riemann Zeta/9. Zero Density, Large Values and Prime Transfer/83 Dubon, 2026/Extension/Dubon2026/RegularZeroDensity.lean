import Dubon2026.SelectedMeanMotion
import Dubon2026.HeightLimitTransfer

/-! # The actual vertical zero density at differentiable zero-free endpoints -/

namespace Dubon2026

open Filter Set
open scoped Topology

theorem tendsto_zeroDensity_regular_endpoints {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) {l u dl du : ℝ} (hlu : l ≤ u)
    (hl : ∀ s : ℂ, s.re = l → dirichletSum a N s ≠ 0)
    (hu : ∀ s : ℂ, s.re = u → dirichletSum a N s ≠ 0)
    (hdl : HasDerivAt (jessenFunction a N) dl l)
    (hdu : HasDerivAt (jessenFunction a N) du u) :
    Tendsto (fun T => (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u T : ℝ) /
      (2 * T)) atTop (𝓝 ((du - dl) / (2 * Real.pi))) := by
  have hsel (T : ℝ) := exists_zero_free_symmetric_height hN (ha.trans_ne one_ne_zero)
    (show max T 0 < max T 0 + 1 by linarith)
  choose H hH hh using hsel
  have hnear : ∀ᶠ T in atTop, T ≤ H T ∧ H T ≤ T + 1 := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hx := hH T
    rw [max_eq_left hT] at hx
    exact ⟨hx.1.le, hx.2.le⟩
  have htop : Tendsto H atTop atTop := tendsto_atTop_mono' _
    (hnear.mono fun _ h => h.1) tendsto_id
  have hpos (T : ℝ) : 0 < H T := lt_of_le_of_lt (le_max_right T 0) (hH T).1
  have hb (T : ℝ) := rectangle_boundary_ne_zero_of_lines (hpos T).le hl hu (hh T)
  have herr : Tendsto (fun T =>
      (verticalZeroCount a N hN (ha.trans_ne one_ne_zero) l u (H T) : ℝ) / (2 * H T) -
        (verticalLogDerivMean a N u (H T) - verticalLogDerivMean a N l (H T)) /
          (2 * Real.pi)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      ((htop.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).const_div_atTop ((2 : ℝ) ^ N))
    exact Filter.Eventually.of_forall fun T => by
      simpa only [Real.norm_eq_abs] using
        abs_zeroDensity_sub_verticalLogDerivMean_le hN ha hlu (hpos T) (hb T)
  have hleft := tendsto_verticalLogDerivMean_selected hN ha hl hdl htop (Filter.Eventually.of_forall hh)
  have hright := tendsto_verticalLogDerivMean_selected hN ha hu hdu htop (Filter.Eventually.of_forall hh)
  have hmean := (hright.sub hleft).div_const (2 * Real.pi)
  apply tendsto_verticalZeroCount_of_nearby_heights hN (ha.trans_ne one_ne_zero) l u hnear
  convert herr.add hmean using 1 <;> simp

end Dubon2026
