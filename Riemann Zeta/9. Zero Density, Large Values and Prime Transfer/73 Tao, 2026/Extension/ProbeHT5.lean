import Tao2026.SmoothNumberSaddleHTPrimePowerBridge

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def testSlice (y : ℕ) (sigma : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊(y : ℝ) ^ ((1 : ℝ) / k)⌋₊).filter
    (fun p => p.Prime ∧ ¬(p ^ k).Prime),
    (Λ (p ^ k) : ℝ) * ((p ^ k : ℕ) : ℝ) ^ (-sigma)

example (y : ℕ) (sigma : ℝ) :
    smoothSaddleHTPrimePowerRemainder y sigma =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊,
        testSlice y sigma k := by
  classical
  let f : ℕ → ℝ := fun n =>
    if ¬n.Prime then (Λ n : ℝ) * (n : ℝ) ^ (-sigma) else 0
  have hdecomp := Chebyshev.sum_PrimePow_eq_sum_sum f (Nat.cast_nonneg y)
  have hdecomp' :
      (∑ n ∈ Finset.Ioc 0 ⌊(y : ℝ)⌋₊ with IsPrimePow n, f n) =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log y / Real.log 2⌋₊,
          testSlice y sigma k := by
    simpa only [f, testSlice, Finset.sum_filter, ← ite_and, and_assoc]
      using hdecomp
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

@[simp] example (y : ℕ) (sigma : ℝ) : testSlice y sigma 1 = 0 := by
  classical
  unfold testSlice
  apply Finset.sum_eq_zero
  intro p hp
  rw [Finset.mem_filter] at hp
  exact (hp.2.2 (by simpa using hp.2.1)).elim

theorem testPower {p k : ℕ} {sigma : ℝ} (hp : 2 ≤ p) (hk : 2 ≤ k)
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

example {y k : ℕ} {sigma : ℝ} (hy : 2 ≤ y) (hk : 2 ≤ k)
    (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    testSlice y sigma k ≤
      ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ (k - 2) * weightedPrimeLogSum y := by
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
  unfold testSlice weightedPrimeLogSum
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
        exact testPower hpPrime.two_le hk hsigma
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
      calc
        _ ≤
            Real.log p * ((p : ℝ)⁻¹ * q ^ (k - 2)) :=
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

example (K : ℕ) :
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

end

end Tao2026
