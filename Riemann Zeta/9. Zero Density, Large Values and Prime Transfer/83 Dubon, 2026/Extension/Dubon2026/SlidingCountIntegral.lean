import Dubon2026.SlidingZeroCount

/-! # Integrating sliding zero counts

A finite indicator expansion computes the integral exactly. Its coefficients are
the lengths of intersection of the averaging interval with each zero's window.
-/

namespace Dubon2026

open Set MeasureTheory
open scoped BigOperators

noncomputable section

/-- The actual overlap length of a symmetric interval and a unit-radius window. -/
def windowOverlap (T v : ℝ) : ℝ :=
  volume.real (Ioc (-T) T ∩ Ioo (v - 1) (v + 1))

theorem windowOverlap_nonneg (T v : ℝ) : 0 ≤ windowOverlap T v :=
  measureReal_nonneg

theorem windowOverlap_le_two (T v : ℝ) : windowOverlap T v ≤ 2 := by
  have h := measureReal_mono (μ := (volume : Measure ℝ))
    (inter_subset_right : Ioc (-T) T ∩ Ioo (v - 1) (v + 1) ⊆ Ioo (v - 1) (v + 1))
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have he : volume.real (Ioo (v - 1) (v + 1)) = 2 := by
    rw [Real.volume_real_Ioo_of_le (by linarith)]
    ring
  exact he ▸ h

theorem windowOverlap_eq_two {T v : ℝ} (hv : |v| ≤ T - 1) :
    windowOverlap T v = 2 := by
  have hs : Ioo (v - 1) (v + 1) ⊆ Ioc (-T) T := by
    intro t ht
    obtain ⟨h₁, h₂⟩ := abs_le.mp hv
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [windowOverlap, inter_eq_right.mpr hs, Real.volume_real_Ioo_of_le (by linarith)]
  ring

theorem intervalIntegrable_window_indicator (T v c : ℝ) :
    IntervalIntegrable ((Ioo (v - 1) (v + 1)).indicator (fun _ => c)) volume (-T) T := by
  rw [intervalIntegrable_iff]
  have hc : IntegrableOn (fun _ : ℝ => c) (uIoc (-T) T) volume :=
    integrableOn_const (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)
  exact hc.indicator measurableSet_Ioo

theorem integral_window_indicator {T : ℝ} (hT : 0 ≤ T) (v c : ℝ) :
    (∫ t in -T..T, (Ioo (v - 1) (v + 1)).indicator (fun _ => c) t) =
      windowOverlap T v * c := by
  rw [intervalIntegral.integral_of_le (by linarith), setIntegral_indicator measurableSet_Ioo,
    setIntegral_const]
  rfl

theorem integral_slidingZeroCount_eq (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T + 1),
        windowOverlap T s.im * (zeroMultiplicity a N s : ℝ) := by
  classical
  calc
    _ = ∫ t in -T..T, ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T + 1),
        (Ioo (s.im - 1) (s.im + 1)).indicator
          (fun _ => (zeroMultiplicity a N s : ℝ)) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : -T ≤ T)] at ht
      exact slidingZeroCount_eq_sum_indicators a N hN ha l u 1 (abs_le.mpr ht)
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun s _ =>
        intervalIntegrable_window_indicator T s.im (zeroMultiplicity a N s))]
      apply Finset.sum_congr rfl
      intro s _
      exact integral_window_indicator hT s.im (zeroMultiplicity a N s)

theorem integral_slidingZeroCount_le (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) ≤
      2 * (verticalZeroCount a N hN ha l u (T + 1) : ℝ) := by
  rw [integral_slidingZeroCount_eq a N hN ha l u hT, verticalZeroCount,
    Nat.cast_sum, Finset.mul_sum]
  exact Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right
    (windowOverlap_le_two T s.im) (Nat.cast_nonneg _))

theorem le_integral_slidingZeroCount (a : ℕ → ℂ) (N : ℕ)
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (l u : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    2 * (verticalZeroCount a N hN ha l u (T - 1) : ℝ) ≤
      (∫ t in -T..T, (slidingZeroCount a N hN ha l u 1 t : ℝ)) := by
  classical
  rw [integral_slidingZeroCount_eq a N hN ha l u hT, verticalZeroCount,
    Nat.cast_sum, Finset.mul_sum]
  have he : (∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T - 1),
      2 * (zeroMultiplicity a N s : ℝ)) =
      ∑ s ∈ zerosInOpenRectangleFinset a N hN ha l u (T - 1),
        windowOverlap T s.im * (zeroMultiplicity a N s : ℝ) := by
    apply Finset.sum_congr rfl
    intro s hs
    have ht := ((mem_zerosInOpenRectangleFinset a N hN ha l u (T - 1) s).mp hs).2.2.1
    rw [windowOverlap_eq_two ht.le]
  rw [he]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    rw [mem_zerosInOpenRectangleFinset] at hs ⊢
    exact ⟨hs.1, hs.2.1, by linarith [hs.2.2.1], hs.2.2.2⟩
  · intro s _ _
    exact mul_nonneg (windowOverlap_nonneg T s.im) (Nat.cast_nonneg _)

end

end Dubon2026
