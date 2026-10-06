import Dubon2026.PotentialEquicontinuity
import Dubon2026.ConvexDerivativeLimit

/-! # Limits of actual normalized Jessen derivatives away from the limiting corner -/

namespace Dubon2026

open Set Filter
open scoped Topology

theorem tendsto_normalized_jessen_derivatives_of_lt {a : ℕ → ℂ} {α x : ℝ}
    (ha : a 1 = 1)
    (hp : ∀ σ, Tendsto (fun N => normalizedJessen a N σ) atTop (𝓝 (max (α - σ) 0)))
    (hx : x < α) :
    Tendsto (fun N => derivWithin (jessenFunction a N) (Iio x) x / Real.log N)
      atTop (𝓝 (-1)) ∧
    Tendsto (fun N => derivWithin (jessenFunction a N) (Ioi x) x / Real.log N)
      atTop (𝓝 (-1)) := by
  refine tendsto_scaled_convex_derivatives ?_ ?_ (l := x - 1) (u := (x + α) / 2)
    (b := α) ?_ ?_ ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact convexOn_jessenFunction hN (ha.trans_ne one_ne_zero)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  · linarith
  · linarith
  · simpa only [normalizedJessen, neg_one_mul, neg_add_eq_sub,
      max_eq_left (show 0 ≤ α - (x - 1) by linarith)] using hp (x - 1)
  · simpa only [normalizedJessen, neg_one_mul, neg_add_eq_sub,
      max_eq_left (sub_nonneg.mpr hx.le)] using hp x
  · simpa only [normalizedJessen, neg_one_mul, neg_add_eq_sub,
      max_eq_left (show 0 ≤ α - (x + α) / 2 by linarith)] using hp ((x + α) / 2)

theorem tendsto_normalized_jessen_derivatives_of_gt {a : ℕ → ℂ} {α x : ℝ}
    (ha : a 1 = 1)
    (hp : ∀ σ, Tendsto (fun N => normalizedJessen a N σ) atTop (𝓝 (max (α - σ) 0)))
    (hx : α < x) :
    Tendsto (fun N => derivWithin (jessenFunction a N) (Iio x) x / Real.log N)
      atTop (𝓝 0) ∧
    Tendsto (fun N => derivWithin (jessenFunction a N) (Ioi x) x / Real.log N)
      atTop (𝓝 0) := by
  refine tendsto_scaled_convex_derivatives ?_ ?_ (l := (α + x) / 2) (u := x + 1)
    (b := 0) ?_ ?_ ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact convexOn_jessenFunction hN (ha.trans_ne one_ne_zero)
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  · linarith
  · linarith
  · simpa only [normalizedJessen, zero_mul, zero_add,
      max_eq_right (show α - (α + x) / 2 ≤ 0 by linarith)] using hp ((α + x) / 2)
  · simpa only [normalizedJessen, zero_mul, zero_add,
      max_eq_right (sub_nonpos.mpr hx.le)] using hp x
  · simpa only [normalizedJessen, zero_mul, zero_add,
      max_eq_right (show α - (x + 1) ≤ 0 by linarith)] using hp (x + 1)

/-- Replace the nominal log N normalization with the proved terminal-support normalization. -/
theorem tendsto_div_log_lastIndex {a : ℕ → ℂ} {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto (fun N => f N / Real.log N) atTop (𝓝 c))
    (hM : Tendsto (fun N => Real.log (lastIndex a N) / Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N => f N / Real.log (lastIndex a N)) atTop (𝓝 c) := by
  have hh := hf.div hM one_ne_zero
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact div_div_div_cancel_right₀
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne' _ _

end Dubon2026
