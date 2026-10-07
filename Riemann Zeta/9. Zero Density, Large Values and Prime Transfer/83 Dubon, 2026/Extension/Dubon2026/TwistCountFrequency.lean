import Dubon2026.SlidingCountIntegral
import Dubon2026.ZeroCountHeight

/-! # Zero-frequency existence from phase regularity of the actual count

The only additional assumptions are measurability and Haar-almost-everywhere
continuity of the genuine fixed unit-window count. Its boundedness and the
transfer to all heights are derived, rather than supplied as density assumptions.
The regularity assumptions remain to be discharged for arbitrary strip boundaries.
-/

namespace Dubon2026

open Filter MeasureTheory
open scoped Topology

noncomputable section

theorem exists_slidingZeroCount_integral_error_bound {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 1 ≤ T →
      |(verticalZeroCount a N hN ha l u T : ℝ) -
        (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) / 2| ≤ B := by
  obtain ⟨B, hB, hb⟩ := exists_verticalZeroCount_unit_increment_bound hN ha l u
  refine ⟨B, hB, ?_⟩
  intro T hT
  have hl := le_integral_slidingZeroCount a N hN ha l u (by linarith : 0 ≤ T)
  have hu := integral_slidingZeroCount_le a N hN ha l u (by linarith : 0 ≤ T)
  have hp := hb T (T + 1) (by linarith) (by linarith) le_rfl
  have hm := hb (T - 1) T (by linarith) (by linarith) (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem tendsto_slidingZeroCount_density_difference {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T) -
      (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) / (4 * T))
      atTop (𝓝 0) := by
  obtain ⟨B, _, hb⟩ := exists_slidingZeroCount_integral_error_bound hN ha l u
  apply squeeze_zero_norm' ?_
    ((tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop B)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  have hTp : 0 < 2 * T := by linarith
  have he : (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T) -
      (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) / (4 * T) =
      ((verticalZeroCount a N hN ha l u T : ℝ) -
        (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) / 2) / (2 * T) := by
    ring
  rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hTp]
  exact div_le_div_of_nonneg_right (hb T hT) hTp.le

theorem tendsto_zeroDensity_of_twist_count_regular {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ)
    (hm : Measurable (twistZeroCount a N hN ha l u 1))
    (hc : ∀ᵐ z ∂torusHaar N, ContinuousAt (twistZeroCount a N hN ha l u 1) z) :
    Tendsto (fun T : ℝ => (verticalZeroCount a N hN ha l u T : ℝ) / (2 * T))
      atTop (𝓝 ((∫ z, (twistZeroCount a N hN ha l u 1 z : ℝ) ∂torusHaar N) / 2)) := by
  have hh := (tendsto_twistZeroCount_average hN ha l u 1 hm hc).div_const 2
  have hs : Tendsto (fun T : ℝ =>
      (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) / (4 * T))
      atTop (𝓝 ((∫ z, (twistZeroCount a N hN ha l u 1 z : ℝ) ∂torusHaar N) / 2)) := by
    convert hh using 1
    funext T
    simp only [slidingZeroCount_eq_twistZeroCount]
    ring
  have he := (tendsto_slidingZeroCount_density_difference hN ha l u).add hs
  simpa only [sub_add_cancel, zero_add] using he

end

end Dubon2026
