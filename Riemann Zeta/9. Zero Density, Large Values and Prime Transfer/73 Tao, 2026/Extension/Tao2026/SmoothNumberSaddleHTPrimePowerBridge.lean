import Tao2026.SmoothNumberSaddleHTLemmaSix
import Tao2026.SmoothNumberSaddleOuterDecay

/-!
# From HT Lemma 6 to the prime Euler-product loss

The cosine corollary to Hildebrand--Tenenbaum Lemma 6 is a Mangoldt sum over
all prime powers, whereas the Euler-product contraction uses a sum over
primes.  This module performs that split exactly.  The prime contribution is
at most `log y` times the existing saddle cosine loss, and the non-prime
contribution is at most twice an explicit nonnegative prime-power remainder.

Consequently the named Lemma 6 transform estimate gives a checked lower
bound for the precise cosine loss consumed by the global Euler-product
estimate.  Bounding the remainder and the elementary main term in the
source parameter ranges remains separate.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- The prime-supported logarithmically weighted part of the HT cosine sum. -/
noncomputable def smoothSaddleHTPrimeLogCosineSum
    (y : ℕ) (sigma t : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime,
    Real.log p * (p : ℝ) ^ (-sigma) *
      (1 - Real.cos (t * Real.log p))

/-- The non-prime part of the HT cosine sum.  Von Mangoldt support makes this
the higher-prime-power contribution. -/
noncomputable def smoothSaddleHTPrimePowerCosineTail
    (y : ℕ) (sigma t : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬n.Prime),
    (Λ n : ℝ) * (n : ℝ) ^ (-sigma) *
      (1 - Real.cos (t * Real.log n))

/-- The corresponding prime-power mass before inserting the bounded cosine
factor. -/
noncomputable def smoothSaddleHTPrimePowerRemainder
    (y : ℕ) (sigma : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬n.Prime),
    (Λ n : ℝ) * (n : ℝ) ^ (-sigma)

theorem smoothSaddleHTMangoldtCosineSum_eq_prime_add_primePower
    (y : ℕ) (sigma t : ℝ) :
    smoothSaddleHTMangoldtCosineSum y (1 - sigma) t =
      smoothSaddleHTPrimeLogCosineSum y sigma t +
        smoothSaddleHTPrimePowerCosineTail y sigma t := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Icc 1 y) Nat.Prime
    (fun n => (Λ n : ℝ) * (n : ℝ) ^ (-sigma) *
      (1 - Real.cos (t * Real.log n)))
  unfold smoothSaddleHTMangoldtCosineSum smoothSaddleHTPrimeLogCosineSum
    smoothSaddleHTPrimePowerCosineTail
  simp only [show 1 - sigma - 1 = -sigma by ring]
  calc
    (∑ n ∈ Finset.Icc 1 y,
        (Λ n : ℝ) * (n : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log n))) =
      (∑ n ∈ (Finset.Icc 1 y).filter Nat.Prime,
        (Λ n : ℝ) * (n : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log n))) +
      ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬n.Prime),
        (Λ n : ℝ) * (n : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log n)) := hsplit.symm
    _ = (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime,
        Real.log p * (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log p))) +
      ∑ n ∈ (Finset.Icc 1 y).filter (fun n => ¬n.Prime),
        (Λ n : ℝ) * (n : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log n)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime
        (Finset.mem_filter.mp hp).2]

theorem smoothSaddleHTPrimePowerRemainder_nonneg
    (y : ℕ) (sigma : ℝ) :
    0 ≤ smoothSaddleHTPrimePowerRemainder y sigma := by
  unfold smoothSaddleHTPrimePowerRemainder
  exact Finset.sum_nonneg fun n _ =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

theorem smoothSaddleHTPrimePowerCosineTail_nonneg
    (y : ℕ) (sigma t : ℝ) :
    0 ≤ smoothSaddleHTPrimePowerCosineTail y sigma t := by
  unfold smoothSaddleHTPrimePowerCosineTail
  exact Finset.sum_nonneg fun n _ => mul_nonneg
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (by linarith [Real.cos_le_one (t * Real.log n)])

/-- The factor `1-cos` costs at most two on the higher-prime-power tail. -/
theorem smoothSaddleHTPrimePowerCosineTail_le
    (y : ℕ) (sigma t : ℝ) :
    smoothSaddleHTPrimePowerCosineTail y sigma t ≤
      2 * smoothSaddleHTPrimePowerRemainder y sigma := by
  unfold smoothSaddleHTPrimePowerCosineTail
    smoothSaddleHTPrimePowerRemainder
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  let A : ℝ := (Λ n : ℝ) * (n : ℝ) ^ (-sigma)
  have hA : 0 ≤ A :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have hcos : 1 - Real.cos (t * Real.log n) ≤ 2 := by
    linarith [Real.neg_one_le_cos (t * Real.log n)]
  change A * (1 - Real.cos (t * Real.log n)) ≤ 2 * A
  nlinarith

/-- The logarithm on a source prime is bounded by the endpoint logarithm. -/
theorem smoothSaddleHTPrimeLogCosineSum_le
    (y : ℕ) (sigma t : ℝ) :
    smoothSaddleHTPrimeLogCosineSum y sigma t ≤
      Real.log y * smoothSaddleCosineLoss y sigma t := by
  classical
  have hsets : (Finset.Icc 1 y).filter Nat.Prime =
      (Finset.Icc 2 y).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hp
      exact ⟨⟨hp.2.two_le, hp.1.2⟩, hp.2⟩
    · intro hp
      exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
  unfold smoothSaddleHTPrimeLogCosineSum smoothSaddleCosineLoss
  rw [hsets, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.2.pos
  have hpy : (p : ℝ) ≤ y := by exact_mod_cast (Finset.mem_Icc.mp hpData.1).2
  have hlog : Real.log p ≤ Real.log y := Real.log_le_log hpPos hpy
  have hweight : 0 ≤ (p : ℝ) ^ (-sigma) *
      (1 - Real.cos (t * Real.log p)) :=
    mul_nonneg (by positivity)
      (by linarith [Real.cos_le_one (t * Real.log p)])
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right hlog hweight

/-- Exact source-shaped reduction from the Mangoldt cosine sum to the prime
Euler-product loss and an explicit prime-power remainder. -/
theorem smoothSaddleHTMangoldtCosineSum_sub_remainder_div_log_le_cosineLoss
    {y : ℕ} (hy : 2 ≤ y) (sigma t : ℝ) :
    (smoothSaddleHTMangoldtCosineSum y (1 - sigma) t -
        2 * smoothSaddleHTPrimePowerRemainder y sigma) / Real.log y ≤
      smoothSaddleCosineLoss y sigma t := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hsplit := smoothSaddleHTMangoldtCosineSum_eq_prime_add_primePower
    y sigma t
  have hprime := smoothSaddleHTPrimeLogCosineSum_le y sigma t
  have htail := smoothSaddleHTPrimePowerCosineTail_le y sigma t
  rw [div_le_iff₀ hlog]
  rw [hsplit]
  linarith

/-- Assuming the exact transform estimate of HT Lemma 6, its main term gives
a lower bound for the prime cosine loss after the explicit prime-power cost. -/
theorem SmoothSaddleHTMangoldtTransformEstimate.cosineLoss_lower_bound
    (hHT : SmoothSaddleHTMangoldtTransformEstimate)
    {y : ℕ} {sigma ε t : ℝ}
    (hy : 2 ≤ y) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hε : 0 < ε) (hεOne : ε < 1)
    (ht : |t| ≤ smoothSaddleHTFrequencyCeiling y ε) :
    (smoothSaddleHTMangoldtCosineMainTerm y (1 - sigma) t -
        2 * smoothSaddleHTMangoldtError y (1 - sigma) ε -
        2 * smoothSaddleHTPrimePowerRemainder y sigma) / Real.log y ≤
      smoothSaddleCosineLoss y sigma t := by
  have hbeta : 0 < 1 - sigma := sub_pos.mpr hsigmaOne
  have hbetaOne : 1 - sigma < 1 := by linarith
  have hcosine := hHT.cosine hy hbeta hbetaOne hε hεOne ht
  have hbridge :=
    smoothSaddleHTMangoldtCosineSum_sub_remainder_div_log_le_cosineLoss
      hy sigma t
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  rw [abs_le] at hcosine
  rw [div_le_iff₀ hlog] at hbridge ⊢
  linarith

end

end Tao2026
