import Tao2026.SmoothNumberSaddleFourthShellIntegral

/-!
# Indexed iterated-root outer shells

This module abstracts the repeated square-root alphabets used by the second,
third, and fourth outer shells.  It supplies recursive lower and upper
logarithmic envelopes and the doubling family of physical shell heights.
The existing concrete scales and endpoints are recovered definitionally.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

def smoothSaddleIteratedPrimeScale : ℕ → ℕ → ℕ
  | 0, y => y
  | k + 1, y => Nat.sqrt (smoothSaddleIteratedPrimeScale k y)

@[simp] theorem smoothSaddleIteratedPrimeScale_zero (y : ℕ) :
    smoothSaddleIteratedPrimeScale 0 y = y := rfl

@[simp] theorem smoothSaddleIteratedPrimeScale_succ (k y : ℕ) :
    smoothSaddleIteratedPrimeScale (k + 1) y =
      Nat.sqrt (smoothSaddleIteratedPrimeScale k y) := rfl

theorem smoothSaddleIteratedPrimeScale_one (y : ℕ) :
    smoothSaddleIteratedPrimeScale 1 y = smoothSaddleSecondPrimeScale y := by
  rfl

theorem smoothSaddleIteratedPrimeScale_two (y : ℕ) :
    smoothSaddleIteratedPrimeScale 2 y = smoothSaddleThirdPrimeScale y := by
  rfl

theorem smoothSaddleIteratedPrimeScale_three (y : ℕ) :
    smoothSaddleIteratedPrimeScale 3 y = smoothSaddleFourthPrimeScale y := by
  rfl

theorem smoothSaddleIteratedPrimeScale_le (k y : ℕ) :
    smoothSaddleIteratedPrimeScale k y ≤ y := by
  induction k with
  | zero => simp
  | succ k ih =>
      exact (Nat.sqrt_le_self _).trans ih

def smoothSaddleIteratedLogLower (y : ℕ) : ℕ → ℝ
  | 0 => Real.log (y : ℝ)
  | k + 1 => (1 / 2 : ℝ) * smoothSaddleIteratedLogLower y k - Real.log 2

def smoothSaddleIteratedLogUpper (y : ℕ) : ℕ → ℝ
  | 0 => Real.log (y : ℝ)
  | k + 1 => (1 / 2 : ℝ) * smoothSaddleIteratedLogUpper y k

@[simp] theorem smoothSaddleIteratedLogLower_zero (y : ℕ) :
    smoothSaddleIteratedLogLower y 0 = Real.log (y : ℝ) := rfl

@[simp] theorem smoothSaddleIteratedLogLower_succ (y k : ℕ) :
    smoothSaddleIteratedLogLower y (k + 1) =
      (1 / 2 : ℝ) * smoothSaddleIteratedLogLower y k - Real.log 2 := rfl

@[simp] theorem smoothSaddleIteratedLogUpper_zero (y : ℕ) :
    smoothSaddleIteratedLogUpper y 0 = Real.log (y : ℝ) := rfl

@[simp] theorem smoothSaddleIteratedLogUpper_succ (y k : ℕ) :
    smoothSaddleIteratedLogUpper y (k + 1) =
      (1 / 2 : ℝ) * smoothSaddleIteratedLogUpper y k := rfl

theorem smoothSaddleIteratedLogLower_le_log
    {k y : ℕ}
    (hlarge : ∀ j < k, 4 ≤ smoothSaddleIteratedPrimeScale j y) :
    smoothSaddleIteratedLogLower y k ≤
      Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev : 4 ≤ smoothSaddleIteratedPrimeScale k y :=
        hlarge k (Nat.lt_succ_self k)
      have ih' := ih (fun j hj => hlarge j (hj.trans (Nat.lt_succ_self k)))
      calc
        smoothSaddleIteratedLogLower y (k + 1) =
            (1 / 2 : ℝ) * smoothSaddleIteratedLogLower y k - Real.log 2 := rfl
        _ ≤ (1 / 2 : ℝ) *
              Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) -
              Real.log 2 := by gcongr
        _ ≤ Real.log (smoothSaddleIteratedPrimeScale (k + 1) y : ℝ) := by
          simpa only [smoothSaddleIteratedPrimeScale_succ,
            smoothSaddleSecondPrimeScale] using
            half_log_sub_log_two_le_log_smoothSaddleSecondPrimeScale hprev

theorem log_le_smoothSaddleIteratedLogUpper
    {k y : ℕ}
    (hlarge : ∀ j < k, 4 ≤ smoothSaddleIteratedPrimeScale j y) :
    Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ≤
      smoothSaddleIteratedLogUpper y k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hprev : 4 ≤ smoothSaddleIteratedPrimeScale k y :=
        hlarge k (Nat.lt_succ_self k)
      have ih' := ih (fun j hj => hlarge j (hj.trans (Nat.lt_succ_self k)))
      calc
        Real.log (smoothSaddleIteratedPrimeScale (k + 1) y : ℝ) ≤
            (1 / 2 : ℝ) *
              Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) := by
          simpa only [smoothSaddleIteratedPrimeScale_succ,
            smoothSaddleSecondPrimeScale] using
            log_smoothSaddleSecondPrimeScale_le_half_log hprev
        _ ≤ (1 / 2 : ℝ) * smoothSaddleIteratedLogUpper y k := by gcongr
        _ = smoothSaddleIteratedLogUpper y (k + 1) := rfl

theorem smoothSaddleIteratedLogUpper_eq (k y : ℕ) :
    smoothSaddleIteratedLogUpper y k =
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [smoothSaddleIteratedLogUpper_succ, ih, pow_succ]
      ring

theorem smoothSaddleIteratedLogLower_eq (k y : ℕ) :
    smoothSaddleIteratedLogLower y k =
      (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) -
        2 * (1 - (1 / 2 : ℝ) ^ k) * Real.log 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [smoothSaddleIteratedLogLower_succ, ih, pow_succ]
      ring

theorem iteratedRoot_log_bounds
    {k y : ℕ}
    (hlarge : ∀ j < k, 4 ≤ smoothSaddleIteratedPrimeScale j y) :
    (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) -
          2 * (1 - (1 / 2 : ℝ) ^ k) * Real.log 2 ≤
        Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ∧
      Real.log (smoothSaddleIteratedPrimeScale k y : ℝ) ≤
        (1 / 2 : ℝ) ^ k * Real.log (y : ℝ) := by
  constructor
  · rw [← smoothSaddleIteratedLogLower_eq]
    exact smoothSaddleIteratedLogLower_le_log hlarge
  · rw [← smoothSaddleIteratedLogUpper_eq]
    exact log_le_smoothSaddleIteratedLogUpper hlarge

noncomputable def smoothSaddleIndexedOuterUpperHeight (k y : ℕ) : ℝ :=
  (3 * (2 : ℝ) ^ (k - 1) * Real.pi) / Real.log (y : ℝ)

theorem smoothSaddleIndexedOuterUpperHeight_one (y : ℕ) :
    smoothSaddleIndexedOuterUpperHeight 1 y =
      smoothSaddleSecondOuterUpperHeight y := by
  unfold smoothSaddleIndexedOuterUpperHeight smoothSaddleSecondOuterUpperHeight
  norm_num

theorem smoothSaddleIndexedOuterUpperHeight_two (y : ℕ) :
    smoothSaddleIndexedOuterUpperHeight 2 y =
      smoothSaddleThirdOuterUpperHeight y := by
  unfold smoothSaddleIndexedOuterUpperHeight smoothSaddleThirdOuterUpperHeight
  norm_num

theorem smoothSaddleIndexedOuterUpperHeight_three (y : ℕ) :
    smoothSaddleIndexedOuterUpperHeight 3 y =
      smoothSaddleFourthOuterUpperHeight y := by
  unfold smoothSaddleIndexedOuterUpperHeight smoothSaddleFourthOuterUpperHeight
  norm_num

theorem smoothSaddleIndexedOuterUpperHeight_succ
    {k y : ℕ} (hk : 1 ≤ k) :
    smoothSaddleIndexedOuterUpperHeight (k + 1) y =
      2 * smoothSaddleIndexedOuterUpperHeight k y := by
  unfold smoothSaddleIndexedOuterUpperHeight
  have hsub : k + 1 - 1 = (k - 1) + 1 := by omega
  rw [hsub, pow_succ]
  ring

end

end Tao2026
