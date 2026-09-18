import Tao2026.SmoothNumberSaddleHTPrimePowerBridge

/-!
# Hildebrand--Tenenbaum Lemma 5 in the saddle range

This module bounds the higher-prime-power remainder isolated by the
Hildebrand--Tenenbaum Lemma 6 bridge.  It first expands the remainder by
prime-power exponent, then dominates every exponent slice by a geometric
factor times the weighted prime logarithm sum.  Summing the geometric series
and applying the existing Chebyshev estimate gives an explicit `O(log y)`
bound whenever `sigma ≥ 1 / 2`, the range needed at the smooth-number saddle.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

/-- The contribution to the non-prime Mangoldt mass from the `k`th powers of
primes.  The condition that the power itself is not prime keeps the formula
valid also at `k = 1`, where the slice vanishes. -/
noncomputable def smoothSaddleHTPrimePowerExponentSlice
    (y : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊(y : ℝ) ^ ((1 : ℝ) / k)⌋₊).filter
      (fun p => p.Prime ∧ ¬(p ^ k).Prime),
    (Λ (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-sigma)

/-- Exact decomposition of the higher-prime-power remainder by exponent. -/
theorem smoothSaddleHTPrimePowerRemainder_eq_exponent_sum
    (y : ℕ) (sigma : ℝ) :
    smoothSaddleHTPrimePowerRemainder y sigma =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊,
        smoothSaddleHTPrimePowerExponentSlice y sigma k := by
  classical
  let f : ℕ → ℝ := fun n =>
    if ¬n.Prime then (Λ n : ℝ) * (n : ℝ) ^ (-sigma) else 0
  have hdecomp := Chebyshev.sum_PrimePow_eq_sum_sum f (Nat.cast_nonneg y)
  have hdecomp' :
      (∑ n ∈ Finset.Ioc 0 ⌊(y : ℝ)⌋₊ with IsPrimePow n, f n) =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊,
          smoothSaddleHTPrimePowerExponentSlice y sigma k := by
    simpa only [f, smoothSaddleHTPrimePowerExponentSlice, Finset.sum_filter,
      ← ite_and, and_assoc] using hdecomp
  rw [← hdecomp']
  unfold smoothSaddleHTPrimePowerRemainder f
  have hyFloor : ⌊(y : ℝ)⌋₊ = y := by simp
  rw [hyFloor]
  have hset : (Finset.Icc 1 y).filter (fun n => ¬n.Prime) =
      (Finset.Ioc 0 y).filter (fun n => ¬n.Prime) := by
    ext n
    simp [Nat.succ_le_iff]
  rw [hset]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Ioc] at hn
  by_cases hprime : n.Prime
  · simp [hprime]
  by_cases hpp : IsPrimePow n
  · simp [hprime, hpp]
  · have hLambda : Λ n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    simp [hprime, hpp, hLambda]

@[simp] theorem smoothSaddleHTPrimePowerExponentSlice_one
    (y : ℕ) (sigma : ℝ) :
    smoothSaddleHTPrimePowerExponentSlice y sigma 1 = 0 := by
  classical
  unfold smoothSaddleHTPrimePowerExponentSlice
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  exact (hp.2.2 (by simpa using hp.2.1)).elim

/-- In the saddle range, a `k`th-prime-power weight is bounded by the first
prime weight times a geometric factor in `k`. -/
theorem natPrimePow_rpow_neg_le_geometric
    {p k : ℕ} {sigma : ℝ} (hp : 2 ≤ p) (hk : 2 ≤ k)
    (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    ((p ^ k : ℕ) : ℝ) ^ (-sigma) ≤
      (p : ℝ)⁻¹ * ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (k - 2) := by
  let a : ℝ := (p : ℝ) ^ (-sigma)
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have haHalf : a ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_exponent_le hpOne (by linarith)
  have haQ : a ≤ q := by
    exact haHalf.trans (Real.rpow_le_rpow_of_nonpos
      (by norm_num) (by exact_mod_cast hp) (by norm_num))
  have haSq : a ^ 2 ≤ (p : ℝ)⁻¹ := by
    calc
      a ^ 2 ≤ ((p : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by gcongr
      _ = (p : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_neg_one]
  have hkEq : k = 2 + (k - 2) := by omega
  rw [natCast_pow_rpow_neg]
  change a ^ k ≤ (p : ℝ)⁻¹ * q ^ (k - 2)
  rw [hkEq, pow_add]
  simp only [Nat.add_sub_cancel_left]
  exact mul_le_mul haSq (pow_le_pow_left₀ ha0 haQ (k - 2))
    (pow_nonneg ha0 _) (inv_nonneg.mpr (by positivity))

/-- Each exponent slice is controlled by the weighted prime logarithm sum. -/
theorem smoothSaddleHTPrimePowerExponentSlice_le
    {y k : ℕ} {sigma : ℝ} (hy : 2 ≤ y) (hk : 2 ≤ k)
    (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    smoothSaddleHTPrimePowerExponentSlice y sigma k ≤
      ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (k - 2) *
        weightedPrimeLogSum y := by
  classical
  let S : Finset ℕ :=
    (Finset.Ioc 0 ⌊(y : ℝ) ^ ((1 : ℝ) / k)⌋₊).filter
      (fun p => p.Prime ∧ ¬(p ^ k).Prime)
  let P : Finset ℕ := (Finset.Icc 2 y).filter Nat.Prime
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hsubset : S ⊆ P := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime : p.Prime := hpData.2.1
    have hpRoot : (p : ℝ) ≤ (y : ℝ) ^ ((1 : ℝ) / k) :=
      (Nat.le_floor_iff (Real.rpow_nonneg (by positivity) _)).mp
        (Finset.mem_Ioc.mp hpData.1).2
    have hkPos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkOne : (1 : ℝ) / k ≤ 1 := by
      rw [div_le_one hkPos]
      exact_mod_cast (show 1 ≤ k by omega)
    have hrootLe : (y : ℝ) ^ ((1 : ℝ) / k) ≤ y :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ y by omega)) hkOne
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le,
        by exact_mod_cast hpRoot.trans hrootLe⟩, hpPrime⟩
  unfold smoothSaddleHTPrimePowerExponentSlice weightedPrimeLogSum
  change (∑ p ∈ S, (Λ (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-sigma)) ≤
    q ^ (k - 2) * ∑ p ∈ P, Real.log p / p
  rw [Finset.mul_sum]
  calc
    (∑ p ∈ S, (Λ (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-sigma)) ≤
        ∑ p ∈ S, q ^ (k - 2) * (Real.log p / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpPrime : p.Prime := hpData.2.1
      have hpow := show ((p ^ k : ℕ) : ℝ) ^ (-sigma) ≤
          (p : ℝ)⁻¹ * q ^ (k - 2) by
        dsimp [q]
        exact natPrimePow_rpow_neg_le_geometric hpPrime.two_le hk hsigma
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
      calc
        _ ≤ Real.log p * ((p : ℝ)⁻¹ * q ^ (k - 2)) :=
          mul_le_mul_of_nonneg_left hpow
            (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
        _ = q ^ (k - 2) * (Real.log p / p) := by
          rw [div_eq_mul_inv]
          ring
    _ ≤ ∑ p ∈ P, q ^ (k - 2) * (Real.log p / p) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hpP hpS
      have hpData := Finset.mem_filter.mp hpP
      have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.2.pos
      exact mul_nonneg (pow_nonneg hq0 _)
        (div_nonneg (Real.log_nonneg (by exact_mod_cast hpData.2.one_le)) hpPos.le)

/-- A convenient explicit bound for the truncated geometric coefficients. -/
theorem sum_ht_geometric_coefficients_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K,
      ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (k - 2)) ≤
        2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := by
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have hqHalf : (1 / 2 : ℝ) ≤ q := by
    dsimp [q]
    simpa [Real.rpow_neg_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (-1 : ℝ) ≤ -(1 / 2 : ℝ)))
  have hpoint (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
      q ^ (k - 2) ≤ 2 * q ^ (k - 1) := by
    by_cases hkOne : k = 1
    · subst k
      norm_num
    · have hkTwo : 2 ≤ k := by
        have := (Finset.mem_Icc.mp hk).1
        omega
      have hpow0 : 0 ≤ q ^ (k - 2) := pow_nonneg hq0 _
      have hpow : q ^ (k - 1) = q ^ (k - 2) * q := by
        rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
      rw [hpow]
      nlinarith
  have hnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hsum : (∑ j ∈ Finset.range K, q ^ j) ≤ (1 - q)⁻¹ := by
    have hsummable := summable_geometric_of_norm_lt_one hnorm
    have hle := hsummable.sum_le_tsum (Finset.range K)
      (fun j _ => pow_nonneg hq0 j)
    rw [(hasSum_geom_series_inverse q hnorm).tsum_eq] at hle
    simpa only [Ring.inverse_eq_inv] using hle
  change (∑ k ∈ Finset.Icc 1 K, q ^ (k - 2)) ≤ 2 * (1 - q)⁻¹
  calc
    (∑ k ∈ Finset.Icc 1 K, q ^ (k - 2)) ≤
        ∑ k ∈ Finset.Icc 1 K, 2 * q ^ (k - 1) :=
      Finset.sum_le_sum hpoint
    _ = 2 * ∑ k ∈ Finset.Icc 1 K, q ^ (k - 1) := by
      rw [Finset.mul_sum]
    _ = 2 * ∑ j ∈ Finset.range K, q ^ j := by
      congr 1
      rw [Finset.Icc_eq_Ico, Finset.sum_Ico_eq_sum_range]
      simp
    _ ≤ 2 * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left hsum (by norm_num)

/-- Explicit Hildebrand--Tenenbaum Lemma 5 bound in terms of the weighted
prime logarithm sum. -/
theorem smoothSaddleHTPrimePowerRemainder_le_weightedPrimeLogSum
    {y : ℕ} {sigma : ℝ} (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    smoothSaddleHTPrimePowerRemainder y sigma ≤
      (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
        weightedPrimeLogSum y := by
  classical
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  let K : ℕ := ⌊Real.log y / Real.log 2⌋₊
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hW0 : 0 ≤ weightedPrimeLogSum y := by
    unfold weightedPrimeLogSum
    apply Finset.sum_nonneg
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpData.2.one_le))
      (by exact_mod_cast hpData.2.pos.le)
  rw [smoothSaddleHTPrimePowerRemainder_eq_exponent_sum]
  change (∑ k ∈ Finset.Icc 1 K,
      smoothSaddleHTPrimePowerExponentSlice y sigma k) ≤
    (2 * (1 - q)⁻¹) * weightedPrimeLogSum y
  calc
    (∑ k ∈ Finset.Icc 1 K,
        smoothSaddleHTPrimePowerExponentSlice y sigma k) ≤
        ∑ k ∈ Finset.Icc 1 K,
          q ^ (k - 2) * weightedPrimeLogSum y := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hkOne : k = 1
      · subst k
        simp [hW0]
      · exact smoothSaddleHTPrimePowerExponentSlice_le hy (by
          have := (Finset.mem_Icc.mp hk).1
          omega) hsigma
    _ = (∑ k ∈ Finset.Icc 1 K, q ^ (k - 2)) *
        weightedPrimeLogSum y := by
      rw [Finset.sum_mul]
    _ ≤ (2 * (1 - q)⁻¹) * weightedPrimeLogSum y :=
      mul_le_mul_of_nonneg_right (by
        dsimp [q, K]
        exact sum_ht_geometric_coefficients_le K) hW0

/-- Source-strength `O(log y)` bound for the higher-prime-power remainder in
the saddle range `sigma ≥ 1 / 2`. -/
theorem smoothSaddleHTPrimePowerRemainder_le_log
    {y : ℕ} {sigma : ℝ} (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    smoothSaddleHTPrimePowerRemainder y sigma ≤
      (2 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
        (Real.log 4 * (2 + Real.log y)) := by
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have hC0 : 0 ≤ 2 * (1 - q)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (sub_nonneg.mpr hq1.le))
  calc
    smoothSaddleHTPrimePowerRemainder y sigma ≤
        (2 * (1 - q)⁻¹) * weightedPrimeLogSum y := by
      dsimp [q]
      exact smoothSaddleHTPrimePowerRemainder_le_weightedPrimeLogSum hy hsigma
    _ ≤ (2 * (1 - q)⁻¹) * (Real.log 4 * (2 + Real.log y)) :=
      mul_le_mul_of_nonneg_left (weightedPrimeLogSum_le y (by omega)) hC0

end

end Tao2026
