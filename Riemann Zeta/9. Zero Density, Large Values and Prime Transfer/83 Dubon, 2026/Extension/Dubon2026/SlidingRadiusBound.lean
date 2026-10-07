import Dubon2026.SlidingCountIntegral

/-! # Integrating sliding windows of arbitrarily small radius -/

namespace Dubon2026

open Set MeasureTheory
open scoped BigOperators

theorem intervalIntegrable_radius_window_indicator (T v H c : ℝ) :
    IntervalIntegrable ((Ioo (v - H) (v + H)).indicator (fun _ => c)) volume (-T) T := by
  rw [intervalIntegrable_iff]
  have hc : IntegrableOn (fun _ : ℝ => c) (uIoc (-T) T) volume :=
    integrableOn_const (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  exact hc.indicator measurableSet_Ioo

theorem integral_radius_window_indicator_le {T H c : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hc : 0 ≤ c) (v : ℝ) :
    (∫ t in -T..T, (Ioo (v - H) (v + H)).indicator (fun _ => c) t) ≤ 2 * H * c := by
  rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioo,
    setIntegral_const, smul_eq_mul]
  have hm := measureReal_mono (μ := (volume : Measure ℝ))
    (inter_subset_right : Ioc (-T) T ∩ Ioo (v - H) (v + H) ⊆ Ioo (v - H) (v + H))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have he : volume.real (Ioo (v - H) (v + H)) = 2 * H := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  rw [he] at hm
  exact mul_le_mul_of_nonneg_right hm hc

theorem integral_slidingZeroCount_le_radius (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {T H : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ H) :
    (∫ t in -T..T, (slidingZeroCount a N hN ha l u H t : ℝ)) ≤
      2 * H * (verticalZeroCount a N hN ha l u (T + H) : ℝ) := by
  classical
  have he : (∫ t in -T..T, (slidingZeroCount a N hN ha l u H t : ℝ)) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T + H),
        ∫ t in -T..T, (Ioo (s.im - H) (s.im + H)).indicator
          (fun _ => (zeroMultiplicity a N s : ℝ)) t := by
    calc
      _ = ∫ t in -T..T, ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T + H),
          (Ioo (s.im - H) (s.im + H)).indicator
            (fun _ => (zeroMultiplicity a N s : ℝ)) t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by linarith : -T ≤ T)] at ht
        exact slidingZeroCount_eq_sum_indicators a N hN ha l u H (abs_le.mpr ht)
      _ = _ := intervalIntegral.integral_finsetSum
        (fun s _ => intervalIntegrable_radius_window_indicator T s.im H (zeroMultiplicity a N s))
  rw [he, verticalZeroCount, Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun s _ =>
    integral_radius_window_indicator_le hT hH (Nat.cast_nonneg _) s.im)

end Dubon2026
