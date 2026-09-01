import GafniTao.FordExponentialSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Ford's logarithmic Taylor remainder, equation (5.1)

Ford's shifted exponential-sum argument uses the alternating Taylor
polynomial for `log (1+x)` at the closed endpoint `x = 1`.  The usual
open-disc geometric-series bound does not cover that endpoint.  Here the
remainder is represented by a nonnegative interval integral, yielding the
literal `x^(k+1)/(k+1)` error in equation (5.1).
-/

open scoped Interval
open MeasureTheory intervalIntegral Set

namespace GafniTao

noncomputable section

/-- The first `k` terms `x - x²/2 + ... + (-1)^(k-1)x^k/k` in Ford (5.1). -/
def fordLogTaylor (k : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, (-1 : ℝ) ^ j * x ^ (j + 1) / (j + 1)

/-- The signed integral remainder for the alternating logarithm expansion. -/
def fordLogRemainderIntegral (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t in 0..x, t ^ k / (1 + t)

theorem intervalIntegrable_fordLogRemainder
    {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => t ^ k / (1 + t)) volume 0 x := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ k / (1 + t)) (uIcc 0 x) := by
    apply ContinuousOn.div
    · exact continuousOn_pow k
    · exact (continuous_const.add continuous_id).continuousOn
    · intro t ht
      rw [uIcc_of_le hx] at ht
      rcases ht with ⟨ht0, _⟩
      linarith
  exact hcont.intervalIntegrable

theorem fordLogRemainderIntegral_zero {x : ℝ} (hx : 0 ≤ x) :
    fordLogRemainderIntegral 0 x = Real.log (1 + x) := by
  unfold fordLogRemainderIntegral
  simp only [pow_zero, one_div]
  simp only [add_comm (1 : ℝ)]
  rw [intervalIntegral.integral_comp_add_right (fun y : ℝ => y⁻¹) 1]
  rw [integral_inv_of_pos (by norm_num) (by linarith)]
  simp

theorem fordLogRemainderIntegral_rec
    {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    fordLogRemainderIntegral k x + fordLogRemainderIntegral (k + 1) x =
      x ^ (k + 1) / (k + 1) := by
  unfold fordLogRemainderIntegral
  rw [← intervalIntegral.integral_add
    (intervalIntegrable_fordLogRemainder (k := k) hx)
    (intervalIntegrable_fordLogRemainder (k := k + 1) hx)]
  calc
    (∫ t in 0..x, t ^ k / (1 + t) + t ^ (k + 1) / (1 + t)) =
        ∫ t in 0..x, t ^ k := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hden : 1 + t ≠ 0 := by
        rw [uIcc_of_le hx] at ht
        rcases ht with ⟨ht0, _⟩
        linarith
      simp only
      rw [pow_succ]
      field_simp
    _ = x ^ (k + 1) / (k + 1) := by simp

/-- Exact signed integral form of the logarithmic remainder. -/
theorem ford_log_remainder_integral_representation
    {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    (-1 : ℝ) ^ k * (Real.log (1 + x) - fordLogTaylor k x) =
      fordLogRemainderIntegral k x := by
  induction k with
  | zero => simp [fordLogTaylor, fordLogRemainderIntegral_zero hx]
  | succ k ih =>
      rw [fordLogTaylor, Finset.sum_range_succ]
      change (-1 : ℝ) ^ (k + 1) *
          (Real.log (1 + x) -
            (fordLogTaylor k x + (-1 : ℝ) ^ k * x ^ (k + 1) / (k + 1))) = _
      have hrec := fordLogRemainderIntegral_rec (k := k) hx
      have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
        rw [← pow_add]
        simp [← two_mul]
      calc
        (-1 : ℝ) ^ (k + 1) *
            (Real.log (1 + x) -
              (fordLogTaylor k x +
                (-1 : ℝ) ^ k * x ^ (k + 1) / (k + 1))) =
            -((-1 : ℝ) ^ k *
              (Real.log (1 + x) - fordLogTaylor k x)) +
                x ^ (k + 1) / (k + 1) := by
          rw [pow_succ]
          field_simp
          ring_nf at hsign
          ring_nf
          rw [hsign]
          ring
        _ = -fordLogRemainderIntegral k x +
              x ^ (k + 1) / (k + 1) := by rw [ih]
        _ = fordLogRemainderIntegral (k + 1) x := by linarith

theorem fordLogRemainderIntegral_nonneg
    {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ fordLogRemainderIntegral k x := by
  unfold fordLogRemainderIntegral
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  exact div_nonneg (pow_nonneg ht0 _) (by linarith)

theorem fordLogRemainderIntegral_le
    {k : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    fordLogRemainderIntegral k x ≤ x ^ (k + 1) / (k + 1) := by
  unfold fordLogRemainderIntegral
  have hf := intervalIntegrable_fordLogRemainder (k := k) hx
  have hg : IntervalIntegrable (fun t : ℝ => t ^ k) volume 0 x :=
    (continuous_pow k).intervalIntegrable 0 x
  calc
    (∫ t in 0..x, t ^ k / (1 + t)) ≤ ∫ t in 0..x, t ^ k := by
      apply intervalIntegral.integral_mono_on hx hf hg
      intro t ht
      exact div_le_self (pow_nonneg ht.1 _) (by linarith [ht.1])
    _ = x ^ (k + 1) / (k + 1) := by simp

/-- Ford's equation (5.1), including its closed endpoint `x = 1`. -/
theorem ford_equation_5_1
    {k : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |Real.log (1 + x) - fordLogTaylor k x| ≤
      x ^ (k + 1) / (k + 1) := by
  have hrepr := ford_log_remainder_integral_representation (k := k) hx.1
  calc
    |Real.log (1 + x) - fordLogTaylor k x| =
        |(-1 : ℝ) ^ k * (Real.log (1 + x) - fordLogTaylor k x)| := by simp
    _ = |fordLogRemainderIntegral k x| := congrArg abs hrepr
    _ = fordLogRemainderIntegral k x :=
      abs_of_nonneg (fordLogRemainderIntegral_nonneg hx.1)
    _ ≤ x ^ (k + 1) / (k + 1) := fordLogRemainderIntegral_le hx.1

#print axioms ford_log_remainder_integral_representation
#print axioms ford_equation_5_1

end

end GafniTao
