import TaoTrudgianYang2025.PointMeanExponentialOverlap

/-!
Adapted from node 74 `GafniTao/HeathBrownExponentialIntegralOverlap.lean` to the current native
foundation. No adjacent extension or new dependency pin is imported.

# Exponential overlap inside a local second-moment integral

This is the finite Tonelli/overlap step used after Heath--Brown's Lemma 3.
For a unit-separated set of ordinates, the sum of the translated
`exp (-|x|)` kernels costs an absolute factor four.  The theorem keeps the
actual kernel and performs the interchange with the local second-moment
integral; it is not a cardinality estimate detached from that integral.
-/

open Finset MeasureTheory
open scoped BigOperators Interval

namespace TaoTrudgianYang2025

noncomputable section

open RiemannZeta.GuthMaynard

/-- The exponential kernel times a continuous function is interval
integrable on every finite interval. -/
theorem intervalIntegrable_exp_neg_abs_sub_mul
    (f : ℝ → ℝ) (hf : Continuous f) (t a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (-|t - u|) * f u) volume a b := by
  apply Continuous.intervalIntegrable
  fun_prop

/-- Finite interchange for the exact translated exponential kernels. -/
theorem sum_intervalIntegral_exp_neg_abs_sub_mul_eq
    (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    ∑ t ∈ W, (∫ u in a..b, Real.exp (-|t - u|) * f u) =
      ∫ u in a..b, ∑ t ∈ W, Real.exp (-|t - u|) * f u := by
  exact (intervalIntegral.integral_finsetSum fun t ht ↦
    intervalIntegrable_exp_neg_abs_sub_mul f hf t a b).symm

/-- Heath--Brown's bounded-overlap consumer: summing the exact exponential
local moments over a unit-separated family costs at most four times the
underlying second moment on the common interval. -/
theorem sum_intervalIntegral_exp_neg_abs_sub_mul_le_four
    (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (hNonneg : ∀ u, 0 ≤ f u) (a b : ℝ) (hab : a ≤ b)
    (hSep : IsSeparated 1 W) :
    ∑ t ∈ W, (∫ u in a..b, Real.exp (-|t - u|) * f u) ≤
      4 * ∫ u in a..b, f u := by
  rw [sum_intervalIntegral_exp_neg_abs_sub_mul_eq W f hf a b]
  calc
    (∫ u in a..b, ∑ t ∈ W, Real.exp (-|t - u|) * f u) ≤
        ∫ u in a..b, 4 * f u := by
      apply intervalIntegral.integral_mono hab
      · exact (continuous_finsetSum W fun t _ ↦ by fun_prop).intervalIntegrable a b
      · exact (hf.const_mul 4).intervalIntegrable a b
      · intro u
        calc
          ∑ t ∈ W, Real.exp (-|t - u|) * f u =
              (∑ t ∈ W, Real.exp (-|t - u|)) * f u := by
                rw [Finset.sum_mul]
          _ ≤ 4 * f u := mul_le_mul_of_nonneg_right
            (sum_exp_neg_abs_sub_le_four W u hSep) (hNonneg u)
    _ = 4 * ∫ u in a..b, f u :=
      intervalIntegral.integral_const_mul 4 f

/-- Specialization to the actual critical-line local second-moment
integrand. -/
theorem sum_intervalIntegral_exp_kernel_zeta_sq_le_four
    (W : Finset ℝ) (a b : ℝ) (hab : a ≤ b)
    (hSep : IsSeparated 1 W) :
    ∑ t ∈ W,
        (∫ u in a..b,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
      4 * ∫ u in a..b, zetaMomentCriticalNorm u ^ (2 : ℕ) := by
  exact sum_intervalIntegral_exp_neg_abs_sub_mul_le_four W
    (fun u : ℝ ↦ zetaMomentCriticalNorm u ^ (2 : ℕ))
    (continuous_zetaMomentCriticalNorm.pow 2) (fun u ↦ sq_nonneg _) a b hab hSep

/-- The truncated translated intervals occurring in Heath--Brown's Lemma 3
may be enlarged to one common interval before applying bounded overlap. -/
theorem sum_truncated_exp_kernel_zeta_sq_le_four
    (W : Finset ℝ) (lo hi L : ℝ) (hlohi : lo ≤ hi) (hL : 0 ≤ L)
    (hRange : ∀ t ∈ W, lo ≤ t ∧ t ≤ hi)
    (hSep : IsSeparated 1 W) :
    ∑ t ∈ W,
        (∫ u in t - L..t + L,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
      4 * ∫ u in lo - L..hi + L,
        zetaMomentCriticalNorm u ^ (2 : ℕ) := by
  calc
    ∑ t ∈ W,
        (∫ u in t - L..t + L,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
        ∑ t ∈ W,
          (∫ u in lo - L..hi + L,
            Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htRange := hRange t ht
      apply intervalIntegral.integral_mono_interval
      · linarith
      · linarith
      · linarith
      · filter_upwards with u
        positivity
      · exact intervalIntegrable_exp_neg_abs_sub_mul
          (fun u : ℝ ↦ zetaMomentCriticalNorm u ^ (2 : ℕ))
          (continuous_zetaMomentCriticalNorm.pow 2) t (lo - L) (hi + L)
    _ ≤ 4 * ∫ u in lo - L..hi + L,
        zetaMomentCriticalNorm u ^ (2 : ℕ) := by
      apply sum_intervalIntegral_exp_kernel_zeta_sq_le_four
      · linarith
      · exact hSep

/-- Source-window form of bounded overlap.  If all centres lie in the middle
half of a `2G` interval and their truncation radius fits in the remaining
half, every moving interval is first enlarged to the exact source interval
`[center-G, center+G]`. -/
theorem sum_truncated_exp_kernel_zeta_sq_le_localSecondMoment
    (W : Finset ℝ) (center G L : ℝ) (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hRange : ∀ t ∈ W, center - G / 2 ≤ t ∧ t ≤ center + G / 2)
    (hFit : G / 2 + L ≤ G) (hSep : IsSeparated 1 W) :
    ∑ t ∈ W,
        (∫ u in t - L..t + L,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
      4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ)) := by
  calc
    ∑ t ∈ W,
        (∫ u in t - L..t + L,
          Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) ≤
        ∑ t ∈ W,
          (∫ u in center - G..center + G,
            Real.exp (-|t - u|) * zetaMomentCriticalNorm u ^ (2 : ℕ)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htRange := hRange t ht
      apply intervalIntegral.integral_mono_interval
      · linarith
      · linarith
      · linarith
      · filter_upwards with u
        positivity
      · exact intervalIntegrable_exp_neg_abs_sub_mul
          (fun u : ℝ ↦ zetaMomentCriticalNorm u ^ (2 : ℕ))
          (continuous_zetaMomentCriticalNorm.pow 2) t (center - G) (center + G)
    _ ≤ 4 * ∫ u in center - G..center + G,
        zetaMomentCriticalNorm u ^ (2 : ℕ) := by
      exact sum_intervalIntegral_exp_kernel_zeta_sq_le_four W
        (center - G) (center + G) (by linarith) hSep
    _ = 4 * (∫ u in center - G..center + G, zetaMomentCriticalNorm u ^ (2 : ℕ)) := by
      rfl


end

end TaoTrudgianYang2025
