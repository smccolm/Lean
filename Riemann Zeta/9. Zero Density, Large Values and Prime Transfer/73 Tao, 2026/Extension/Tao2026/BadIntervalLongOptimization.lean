import Tao2026.BadIntervalCofactorSieve

/-!
# Quantitative optimization of the long bad-interval sieve

This module carries the real-variable optimization following the exact
cofactor large sieve through the canonical-degree exponential estimate.  It
extracts the paper's explicit reciprocal factor `H / (8 k log(2p₀))`, proves
the exact floor-maximality lower bound on `k`, absorbs the leading `H`, and
leaves the later scale split, saddle estimate, and fiber summation explicit.
-/

namespace Tao2026

open Filter

noncomputable section

/-- The unpowered base in the canonical cofactor large-sieve weight. -/
def badIntervalCofactorSieveBase (p₀ H k : ℕ) : ℝ :=
  (((badIntervalUpperPrimes p₀).card : ℝ) *
    ((H : ℝ) / (2 * p₀))) / (2 * k)

def badIntervalCofactorSieveWeight (p₀ H k : ℕ) : ℝ :=
  (badIntervalCofactorSieveBase p₀ H k) ^ k

/-! ## The lower bound on the canonical cofactor degree -/

/-- Maximality of Tao's canonical cofactor degree, before the quotient
defining the cofactor budget is expanded. -/
theorem badIntervalCofactorSieveDegree_next_power_gt
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀) :
    badIntervalCofactorBudget x p₀ + 1 <
      (2 * p₀) ^ (2 * (badIntervalCofactorSieveDegree x p₀ + 1)) := by
  simpa only [badIntervalCofactorSieveDegree] using
    (factorialSieveDegree_next_power_gt
      (x := badIntervalCofactorBudget x p₀) (a := 2 * p₀)
      (by omega : 2 ≤ 2 * p₀))

/-- Expanding `⌊2x / p₀²⌋` in the preceding maximality estimate gives the
exact natural-number inequality underlying Tao's lower bound on `k`. -/
theorem two_mul_x_lt_badIntervalCofactorSieveDegree_power
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀) :
    2 * x < (2 * p₀) ^
      (2 * badIntervalCofactorSieveDegree x p₀ + 4) := by
  let k := badIntervalCofactorSieveDegree x p₀
  have hp₀pos : 0 < p₀ := by omega
  have hd : 0 < p₀ ^ 2 := pow_pos hp₀pos 2
  have hdiv : 2 * x <
      (badIntervalCofactorBudget x p₀ + 1) * p₀ ^ 2 := by
    simpa only [badIntervalCofactorBudget] using
      ((Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (2 * x / p₀ ^ 2)))
  have hnext : badIntervalCofactorBudget x p₀ + 1 <
      (2 * p₀) ^ (2 * (k + 1)) := by
    simpa only [k] using
      (badIntervalCofactorSieveDegree_next_power_gt (x := x) hp₀)
  have hpSq : p₀ ^ 2 ≤ (2 * p₀) ^ 2 := by
    nlinarith [sq_nonneg (p₀ : ℤ)]
  calc
    2 * x < (badIntervalCofactorBudget x p₀ + 1) * p₀ ^ 2 := hdiv
    _ < (2 * p₀) ^ (2 * (k + 1)) * p₀ ^ 2 :=
      Nat.mul_lt_mul_of_pos_right hnext hd
    _ ≤ (2 * p₀) ^ (2 * (k + 1)) * (2 * p₀) ^ 2 := by
      gcongr
    _ = (2 * p₀) ^ (2 * k + 4) := by
      rw [← pow_add]
      congr 1

/-- Logarithmic form of the canonical-degree lower bound:
`log(2x) / log(2p₀) < 2k + 4`. -/
theorem badIntervalCofactorSieveDegree_log_ratio_lt
    {x p₀ : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀) :
    Real.log (((2 * x : ℕ) : ℝ)) /
        Real.log (((2 * p₀ : ℕ) : ℝ)) <
      ((2 * badIntervalCofactorSieveDegree x p₀ + 4 : ℕ) : ℝ) := by
  have hlogBase : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hleft : (0 : ℝ) < ((2 * x : ℕ) : ℝ) := by positivity
  have hnat :=
    two_mul_x_lt_badIntervalCofactorSieveDegree_power (x := x) hp₀
  have hcast : ((2 * x : ℕ) : ℝ) <
      (((2 * p₀) ^
        (2 * badIntervalCofactorSieveDegree x p₀ + 4) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hright : (0 : ℝ) <
      (((2 * p₀) ^
        (2 * badIntervalCofactorSieveDegree x p₀ + 4) : ℕ) : ℝ) := by
    exact_mod_cast
      (pow_pos (by omega : 0 < 2 * p₀)
        (2 * badIntervalCofactorSieveDegree x p₀ + 4))
  have hlog : Real.log (((2 * x : ℕ) : ℝ)) <
      ((2 * badIntervalCofactorSieveDegree x p₀ + 4 : ℕ) : ℝ) *
        Real.log (((2 * p₀ : ℕ) : ℝ)) := by
    calc
      Real.log (((2 * x : ℕ) : ℝ)) <
          Real.log ((((2 * p₀) ^
            (2 * badIntervalCofactorSieveDegree x p₀ + 4) : ℕ) : ℝ)) :=
        Real.strictMonoOn_log hleft hright hcast
      _ = ((2 * badIntervalCofactorSieveDegree x p₀ + 4 : ℕ) : ℝ) *
          Real.log (((2 * p₀ : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
  exact (div_lt_iff₀ hlogBase).2 hlog

/-- The finite version of the paper's displayed quarter-bound.  The
hypothesis `4 ≤ k` is necessary: the claimed algebraic comparison is false
for `k = 2, 3`, which must be treated separately in the eventual scale split. -/
theorem badIntervalCofactorSieveDegree_sub_one_gt_log_ratio_div_four
    {x p₀ : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hk : 4 ≤ badIntervalCofactorSieveDegree x p₀) :
    Real.log (((2 * x : ℕ) : ℝ)) /
        (4 * Real.log (((2 * p₀ : ℕ) : ℝ))) <
      (badIntervalCofactorSieveDegree x p₀ : ℝ) - 1 := by
  have hlogBase : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hratio := badIntervalCofactorSieveDegree_log_ratio_lt hx hp₀
  have hrewrite : Real.log (((2 * x : ℕ) : ℝ)) /
      (4 * Real.log (((2 * p₀ : ℕ) : ℝ))) =
      (Real.log (((2 * x : ℕ) : ℝ)) /
        Real.log (((2 * p₀ : ℕ) : ℝ))) / 4 := by
    field_simp
  norm_num [Nat.cast_add, Nat.cast_mul] at hratio
  have hkReal : (4 : ℝ) ≤ badIntervalCofactorSieveDegree x p₀ := by
    exact_mod_cast hk
  calc
    Real.log (((2 * x : ℕ) : ℝ)) /
          (4 * Real.log (((2 * p₀ : ℕ) : ℝ))) =
        (Real.log (((2 * x : ℕ) : ℝ)) /
          Real.log (((2 * p₀ : ℕ) : ℝ))) / 4 := hrewrite
    _ < (2 * (badIntervalCofactorSieveDegree x p₀ : ℝ) + 4) / 4 := by
      exact div_lt_div_of_pos_right
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio) (by norm_num)
    _ ≤ (badIntervalCofactorSieveDegree x p₀ : ℝ) - 1 := by
      linarith

/-- The corrected comparison valid throughout the source range `k ≥ 2`.
Replacing the paper's invalid factor `1/4` by `1/8` retains enough decay for
the final weak `z`-power saving. -/
theorem badIntervalCofactorSieveDegree_sub_one_gt_log_ratio_div_eight
    {x p₀ : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hk : 2 ≤ badIntervalCofactorSieveDegree x p₀) :
    Real.log (((2 * x : ℕ) : ℝ)) /
        (8 * Real.log (((2 * p₀ : ℕ) : ℝ))) <
      (badIntervalCofactorSieveDegree x p₀ : ℝ) - 1 := by
  have hratio := badIntervalCofactorSieveDegree_log_ratio_lt hx hp₀
  have hrewrite : Real.log (((2 * x : ℕ) : ℝ)) /
      (8 * Real.log (((2 * p₀ : ℕ) : ℝ))) =
      (Real.log (((2 * x : ℕ) : ℝ)) /
        Real.log (((2 * p₀ : ℕ) : ℝ))) / 8 := by
    field_simp
  norm_num [Nat.cast_add, Nat.cast_mul] at hratio
  have hkReal : (2 : ℝ) ≤ badIntervalCofactorSieveDegree x p₀ := by
    exact_mod_cast hk
  calc
    Real.log (((2 * x : ℕ) : ℝ)) /
          (8 * Real.log (((2 * p₀ : ℕ) : ℝ))) =
        (Real.log (((2 * x : ℕ) : ℝ)) /
          Real.log (((2 * p₀ : ℕ) : ℝ))) / 8 := hrewrite
    _ < (2 * (badIntervalCofactorSieveDegree x p₀ : ℝ) + 4) / 8 := by
      exact div_lt_div_of_pos_right
        (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hratio) (by norm_num)
    _ ≤ (badIntervalCofactorSieveDegree x p₀ : ℝ) - 1 := by
      linarith

/-- The source upper range `p₀ ≤ x^0.15`, encoded without real rounding as
`p₀^20 ≤ x^3`, eventually forces the canonical cofactor degree to be at
least two. -/
theorem two_le_badIntervalCofactorSieveDegree_of_pow_twenty_le
    {x p₀ : ℕ} (hx : 8 ^ 10 ≤ x) (hp₀ : 1 ≤ p₀)
    (hscale : p₀ ^ 20 ≤ x ^ 3) :
    2 ≤ badIntervalCofactorSieveDegree x p₀ := by
  have hpSixty : p₀ ^ 60 ≤ x ^ 9 := by
    calc
      p₀ ^ 60 = (p₀ ^ 20) ^ 3 := by ring
      _ ≤ (x ^ 3) ^ 3 := Nat.pow_le_pow_left hscale 3
      _ = x ^ 9 := by ring
  have hroot : 8 * p₀ ^ 6 ≤ x := by
    apply (Nat.pow_le_pow_iff_left (by norm_num : 10 ≠ 0)).mp
    calc
      (8 * p₀ ^ 6) ^ 10 = 8 ^ 10 * p₀ ^ 60 := by ring
      _ ≤ x * x ^ 9 := Nat.mul_le_mul hx hpSixty
      _ = x ^ 10 := by ring
  have hmul : (2 * p₀) ^ 4 * p₀ ^ 2 ≤ 2 * x := by
    calc
      (2 * p₀) ^ 4 * p₀ ^ 2 = 2 * (8 * p₀ ^ 6) := by ring
      _ ≤ 2 * x := Nat.mul_le_mul_left 2 hroot
  have hpSqPos : 0 < p₀ ^ 2 := pow_pos (by omega) 2
  have hbudget : (2 * p₀) ^ 4 ≤ badIntervalCofactorBudget x p₀ := by
    rw [badIntervalCofactorBudget]
    exact (Nat.le_div_iff_mul_le hpSqPos).2 hmul
  exact le_badIntervalCofactorSieveDegree_of_power_le hp₀ (by
    simpa only [show 2 * 2 = 4 by norm_num] using hbudget.trans (Nat.le_add_right _ _))

/-- The complementary finite degree branch forces the prime scale to be
large: if `k<4`, then already `2x<(2p₀)^10`. -/
theorem two_mul_x_lt_pow_ten_of_badIntervalCofactorSieveDegree_lt_four
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀)
    (hk : badIntervalCofactorSieveDegree x p₀ < 4) :
    2 * x < (2 * p₀) ^ 10 := by
  exact (two_mul_x_lt_badIntervalCofactorSieveDegree_power (x := x) hp₀).trans_le
    (Nat.pow_le_pow_right (by omega : 0 < 2 * p₀) (by omega))

/-- The unsieved two-orientation cover costs at most `8x/p₀` after
multiplication by `p₀`, provided the source square scale is nonvacuous. -/
theorem p₀_mul_card_scaleNormalizedBadIntervalUnionAt_le
    {x p₀ H : ℕ} (hHp₀ : H < p₀) (hpSq : p₀ ^ 2 ≤ 2 * x) :
    p₀ * (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤ 8 * x := by
  have hcover :=
    card_scaleNormalizedBadIntervalUnionAt_le_two_mul_budget x p₀ H
  have hdiv : badIntervalCofactorBudget x p₀ * p₀ ^ 2 ≤ 2 * x := by
    simpa only [badIntervalCofactorBudget] using
      (Nat.div_mul_le_self (2 * x) (p₀ ^ 2))
  calc
    p₀ * (scaleNormalizedBadIntervalUnionAt x p₀ H).card ≤
        p₀ * (2 * H * (badIntervalCofactorBudget x p₀ + 1)) :=
      Nat.mul_le_mul_left p₀ hcover
    _ ≤ p₀ * (2 * p₀ * (badIntervalCofactorBudget x p₀ + 1)) := by
      gcongr
    _ = 2 * (badIntervalCofactorBudget x p₀ * p₀ ^ 2) +
        2 * p₀ ^ 2 := by ring
    _ ≤ 2 * (2 * x) + 2 * (2 * x) := by gcongr
    _ = 8 * x := by ring

/-- The entire `k<4` fiber has a fixed power saving.  This supplies the
large-`p₀` branch missing from the paper's invalid use of the quarter-bound at
degrees two and three. -/
theorem card_scaleNormalizedBadIntervalUnionAt_le_of_degree_lt_four
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀) (hHp₀ : H < p₀)
    (hpSq : p₀ ^ 2 ≤ 2 * x)
    (hk : badIntervalCofactorSieveDegree x p₀ < 4) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      4096 * (x : ℝ) ^ ((9 : ℝ) / 10) := by
  have hpow :=
    two_mul_x_lt_pow_ten_of_badIntervalCofactorSieveDegree_lt_four hp₀ hk
  norm_num [mul_pow] at hpow
  have hxPow : x ≤ 512 * p₀ ^ 10 := by omega
  have hscalePow : x ≤ (512 * p₀) ^ 10 := by
    calc
      x ≤ 512 * p₀ ^ 10 := hxPow
      _ ≤ 512 ^ 10 * p₀ ^ 10 := by
        gcongr
        norm_num
      _ = (512 * p₀) ^ 10 := by rw [mul_pow]
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hroot : (x : ℝ) ^ ((1 : ℝ) / 10) ≤ 512 * (p₀ : ℝ) := by
    calc
      (x : ℝ) ^ ((1 : ℝ) / 10) ≤
          (((512 * p₀ : ℕ) : ℝ) ^ (10 : ℕ)) ^ ((1 : ℝ) / 10) := by
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hscalePow)
          (by norm_num)
      _ = 512 * (p₀ : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
  have hcardNat := p₀_mul_card_scaleNormalizedBadIntervalUnionAt_le
    (x := x) hHp₀ hpSq
  have hcardReal : (p₀ : ℝ) *
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      8 * (x : ℝ) := by exact_mod_cast hcardNat
  have hmul : ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 10) ≤ 4096 * (x : ℝ) := by
    calc
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) *
          (x : ℝ) ^ ((1 : ℝ) / 10) ≤
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) *
          (512 * (p₀ : ℝ)) := by gcongr
      _ = 512 * ((p₀ : ℝ) *
          (scaleNormalizedBadIntervalUnionAt x p₀ H).card) := by ring
      _ ≤ 512 * (8 * (x : ℝ)) := by gcongr
      _ = 4096 * (x : ℝ) := by ring
  apply le_of_mul_le_mul_right ?_
    (Real.rpow_pos_of_pos hxpos ((1 : ℝ) / 10))
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) *
        (x : ℝ) ^ ((1 : ℝ) / 10) ≤ 4096 * (x : ℝ) := hmul
    _ = (4096 * (x : ℝ) ^ ((9 : ℝ) / 10)) *
        (x : ℝ) ^ ((1 : ℝ) / 10) := by
      calc
        4096 * (x : ℝ) = 4096 * (x : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = 4096 * ((x : ℝ) ^ ((9 : ℝ) / 10) *
            (x : ℝ) ^ ((1 : ℝ) / 10)) := by
          rw [← Real.rpow_add hxpos]
          norm_num
        _ = _ := by ring

/-- The canonical degree times its logarithmic prime scale is bounded
uniformly by the logarithm of the cofactor budget. -/
theorem eight_mul_badIntervalCofactorSieveDegree_mul_log_le
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀) :
    8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log (((2 * p₀ : ℕ) : ℝ)) ≤
      4 * Real.log (((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ)) := by
  have hloga : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hk : (badIntervalCofactorSieveDegree x p₀ : ℝ) ≤
      Real.log (((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ)) /
        (2 * Real.log (((2 * p₀ : ℕ) : ℝ))) := by
    simpa only [badIntervalCofactorSieveDegree] using
      (factorialSieveDegree_cast_le
        (x := badIntervalCofactorBudget x p₀) (a := 2 * p₀)
        (by omega : 2 ≤ 2 * p₀))
  calc
    8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
          Real.log (((2 * p₀ : ℕ) : ℝ)) ≤
        8 * (Real.log (((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ)) /
          (2 * Real.log (((2 * p₀ : ℕ) : ℝ)))) *
            Real.log (((2 * p₀ : ℕ) : ℝ)) := by
      gcongr
    _ = 4 * Real.log
        (((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ)) := by
      field_simp [ne_of_gt hloga]
      ring

/-- A source-scale wrapper independent of `p₀`: it is enough for the length
power to dominate `4 log(2x+1)`. -/
theorem eight_mul_badIntervalCofactorSieveDegree_mul_log_le_of_x
    {x p₀ H : ℕ} (hp₀ : 1 ≤ p₀)
    (hscale : 4 * Real.log (((2 * x + 1 : ℕ) : ℝ)) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50)) :
    8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log (((2 * p₀ : ℕ) : ℝ)) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50) := by
  have hbudget : badIntervalCofactorBudget x p₀ + 1 ≤ 2 * x + 1 := by
    have hdiv : 2 * x / p₀ ^ 2 ≤ 2 * x := Nat.div_le_self _ _
    simpa only [badIntervalCofactorBudget] using Nat.add_le_add_right hdiv 1
  have hlog : Real.log
      (((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ)) ≤
      Real.log (((2 * x + 1 : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hbudget)
  exact (eight_mul_badIntervalCofactorSieveDegree_mul_log_le hp₀).trans
    ((mul_le_mul_of_nonneg_left hlog (by norm_num)).trans hscale)

/-- Tao's literal long-interval cutoff eventually dominates the logarithmic
scale needed for the stronger denominator absorption. -/
theorem eventually_four_log_two_mul_add_one_le_lengthCutoff_rpow :
    ∀ᶠ x : ℕ in atTop,
      4 * Real.log (((2 * x + 1 : ℕ) : ℝ)) ≤
        (taoTypicalLengthCutoff x : ℝ) ^ ((3 : ℝ) / 50) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto (fun x : ℕ =>
      (Real.log x) ^ ((1 : ℝ) / 5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hlog
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ)),
    hroot.eventually (eventually_ge_atTop (8 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hlogTwo hrootEight hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hlogPos : 0 < Real.log (x : ℝ) :=
    lt_of_lt_of_le (by norm_num) hlogTwo
  have harg : (((2 * x + 1 : ℕ) : ℝ)) ≤ 3 * (x : ℝ) := by
    norm_num
    exact_mod_cast (by omega : 2 * x + 1 ≤ 3 * x)
  have hlogArg : Real.log (((2 * x + 1 : ℕ) : ℝ)) ≤
      Real.log (3 * (x : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) harg
  have hlogThree : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlogUpper : Real.log (((2 * x + 1 : ℕ) : ℝ)) ≤
      2 * Real.log (x : ℝ) := by
    calc
      Real.log (((2 * x + 1 : ℕ) : ℝ)) ≤ Real.log (3 * (x : ℝ)) := hlogArg
      _ = Real.log 3 + Real.log (x : ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hxpos)]
      _ ≤ 2 * Real.log (x : ℝ) := by linarith
  have heighteen : 8 * Real.log (x : ℝ) ≤
      (Real.log (x : ℝ)) ^ ((6 : ℝ) / 5) := by
    calc
      8 * Real.log (x : ℝ) ≤
          (Real.log (x : ℝ)) ^ ((1 : ℝ) / 5) * Real.log (x : ℝ) := by
        gcongr
      _ = (Real.log (x : ℝ)) ^ ((6 : ℝ) / 5) := by
        calc
          (Real.log (x : ℝ)) ^ ((1 : ℝ) / 5) * Real.log (x : ℝ) =
              (Real.log (x : ℝ)) ^ ((1 : ℝ) / 5) *
                (Real.log (x : ℝ)) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (Real.log (x : ℝ)) ^ ((1 : ℝ) / 5 + 1) :=
            (Real.rpow_add hlogPos _ _).symm
          _ = (Real.log (x : ℝ)) ^ ((6 : ℝ) / 5) := by norm_num
  have hcut := taoTypicalLengthCutoff_spec x
  calc
    4 * Real.log (((2 * x + 1 : ℕ) : ℝ)) ≤
        8 * Real.log (x : ℝ) := by linarith
    _ ≤ (Real.log (x : ℝ)) ^ ((6 : ℝ) / 5) := heighteen
    _ = ((Real.log (x : ℝ)) ^ (20 : ℕ)) ^ ((3 : ℝ) / 50) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogPos.le]
      congr 1
      norm_num
    _ ≤ (taoTypicalLengthCutoff x : ℝ) ^ ((3 : ℝ) / 50) := by
      exact Real.rpow_le_rpow (by positivity) hcut (by norm_num)

/-- Eventual source-facing discharge of the stronger denominator comparison
for every long interval and every positive prime scale. -/
theorem eventually_canonicalCofactorDenominator_le_of_long :
    ∀ᶠ x : ℕ in atTop, ∀ {p₀ H : ℕ},
      1 ≤ p₀ → taoTypicalLengthCutoff x ≤ H →
      8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
          Real.log (((2 * p₀ : ℕ) : ℝ)) ≤
        (H : ℝ) ^ ((3 : ℝ) / 50) := by
  filter_upwards
    [eventually_four_log_two_mul_add_one_le_lengthCutoff_rpow]
      with x hscale
  intro p₀ H hp₀ hlong
  have hcutToH : (taoTypicalLengthCutoff x : ℝ) ^ ((3 : ℝ) / 50) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50) := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlong) (by norm_num)
  exact eight_mul_badIntervalCofactorSieveDegree_mul_log_le_of_x hp₀
    (hscale.trans hcutToH)

theorem badIntervalCofactorSieveBase_nonneg (p₀ H k : ℕ) :
    0 ≤ badIntervalCofactorSieveBase p₀ H k := by
  rw [badIntervalCofactorSieveBase]
  exact div_nonneg
    (mul_nonneg (by positivity) (div_nonneg (by positivity) (by positivity)))
    (by positivity)

/-- The PNT cardinality estimate gives the exact source-shaped lower bound
for the unpowered sieve base. -/
theorem badIntervalCofactorSieveBase_ge
    {p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hk : 1 ≤ k)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ)) :
    (H : ℝ) /
        (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      badIntervalCofactorSieveBase p₀ H k := by
  have hpCast : (0 : ℝ) < ((2 * p₀ : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * p₀)
  have hkCast : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  calc
    (H : ℝ) /
          (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ)) =
        ((((2 * p₀ : ℕ) : ℝ) /
            (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) *
          ((H : ℝ) / ((2 * p₀ : ℕ) : ℝ))) /
            (2 * (k : ℝ))) := by
      field_simp [ne_of_gt hpCast, ne_of_gt hkCast, ne_of_gt hlog]
      ring
    _ ≤ ((((badIntervalUpperPrimes p₀).card : ℝ) *
          ((H : ℝ) / ((2 * p₀ : ℕ) : ℝ))) /
            (2 * (k : ℝ))) := by
      gcongr
    _ = badIntervalCofactorSieveBase p₀ H k := by
      simp only [badIntervalCofactorSieveBase, Nat.cast_mul, Nat.cast_ofNat]

/-- Raising the preceding lower bound to the natural sieve degree. -/
theorem badIntervalCofactorSieveWeight_ge
    {p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hk : 1 ≤ k)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ)) :
    ((H : ℝ) /
        (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ))) ^ k ≤
      badIntervalCofactorSieveWeight p₀ H k := by
  exact pow_le_pow_left₀ (by positivity)
    (badIntervalCofactorSieveBase_ge hp₀ hk hcard) k

/-- Fixed-fiber estimate with the PNT cardinality replaced by the explicit
source denominator `8 k log(2p₀)`. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_explicitCofactorWeight_le
    {x p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ)) :
    ((H : ℝ) /
        (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ))) ^ k *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
  have hweight := badIntervalCofactorSieveWeight_ge (H := H) hp₀ hk hcard
  have hcardNonneg : 0 ≤
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) := by positivity
  calc
    ((H : ℝ) /
          (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ))) ^ k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        badIntervalCofactorSieveWeight p₀ H k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) :=
      mul_le_mul_of_nonneg_right hweight hcardNonneg
    _ ≤ (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
      simpa only [badIntervalCofactorSieveWeight,
        badIntervalCofactorSieveBase] using
        (scaleNormalizedBadIntervalUnionAt_mul_cofactorSourceWeight_le
          hH hHp₀ hk hkcard hproduct)

/-- Tao's elementary large-`H` step: once `8 k log(2p₀) ≤ H^(1/10)`, the
unpowered sieve base is at least `H^(9/10)`. -/
theorem badIntervalCofactorSieveBase_ge_rpow_nine_tenths
    {p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hsmall : 8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((1 : ℝ) / 10)) :
    (H : ℝ) ^ ((9 : ℝ) / 10) ≤
      badIntervalCofactorSieveBase p₀ H k := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 < Real.log ((2 * p₀ : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hden : 0 < 8 * (k : ℝ) *
      Real.log ((2 * p₀ : ℕ) : ℝ) := by positivity
  calc
    (H : ℝ) ^ ((9 : ℝ) / 10) =
        (H : ℝ) /
          ((H : ℝ) ^ ((1 : ℝ) / 10)) := by
      rw [show (9 : ℝ) / 10 = 1 - 1 / 10 by norm_num,
        Real.rpow_sub hHpos, Real.rpow_one]
    _ ≤ (H : ℝ) /
        (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left hHpos.le hden hsmall
    _ ≤ badIntervalCofactorSieveBase p₀ H k :=
      badIntervalCofactorSieveBase_ge hp₀ hk hcard

theorem badIntervalCofactorSieveWeight_ge_rpow_nine_tenths
    {p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hsmall : 8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((1 : ℝ) / 10)) :
    ((H : ℝ) ^ ((9 : ℝ) / 10)) ^ k ≤
      badIntervalCofactorSieveWeight p₀ H k := by
  exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
    (badIntervalCofactorSieveBase_ge_rpow_nine_tenths
      hp₀ hH hk hcard hsmall) k

/-- The optimized finite fixed-fiber inequality in precisely the form used
before Tao's lower bound on `k-1` is inserted. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_rpow_nine_tenths_le
    {x p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 1 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hsmall : 8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((1 : ℝ) / 10)) :
    ((H : ℝ) ^ ((9 : ℝ) / 10)) ^ k *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
  have hweight := badIntervalCofactorSieveWeight_ge_rpow_nine_tenths
    hp₀ hH hk hcard hsmall
  calc
    ((H : ℝ) ^ ((9 : ℝ) / 10)) ^ k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        badIntervalCofactorSieveWeight p₀ H k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) := by
      gcongr
    _ ≤ (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
      simpa only [badIntervalCofactorSieveWeight,
        badIntervalCofactorSieveBase] using
        (scaleNormalizedBadIntervalUnionAt_mul_cofactorSourceWeight_le
          hH hHp₀ hk hkcard hproduct)

/-- The `H^(0.9k)` fixed-fiber estimate at Tao's canonical cofactor degree. -/
theorem scaleNormalizedBadIntervalUnionAt_mul_canonical_rpow_nine_tenths_le
    {x p₀ H : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hsq : (2 * p₀) ^ 2 ≤ badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ))
    (hsmall : 8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((1 : ℝ) / 10)) :
    ((H : ℝ) ^ ((9 : ℝ) / 10)) ^
          badIntervalCofactorSieveDegree x p₀ *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
  obtain ⟨hk, hkcard, hproduct⟩ :=
    badIntervalCofactorSieveDegree_constraints hp₀ hsq hcard hlarge
  exact scaleNormalizedBadIntervalUnionAt_mul_rpow_nine_tenths_le
    hp₀ hH hHp₀ hk hkcard hproduct hcard hsmall

/-! ## Removing the leading interval-length factor -/

/-- A slightly stronger large-`H` comparison leaves enough exponent slack to
absorb the leading factor `H` in the cofactor-cover estimate. -/
theorem badIntervalCofactorSieveBase_ge_rpow_forty_seven_fiftieths
    {p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hk : 1 ≤ k)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hsmall : 8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50)) :
    (H : ℝ) ^ ((47 : ℝ) / 50) ≤
      badIntervalCofactorSieveBase p₀ H k := by
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog : 0 < Real.log ((2 * p₀ : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hden : 0 < 8 * (k : ℝ) *
      Real.log ((2 * p₀ : ℕ) : ℝ) := by positivity
  calc
    (H : ℝ) ^ ((47 : ℝ) / 50) =
        (H : ℝ) / ((H : ℝ) ^ ((3 : ℝ) / 50)) := by
      rw [show (47 : ℝ) / 50 = 1 - 3 / 50 by norm_num,
        Real.rpow_sub hHpos, Real.rpow_one]
    _ ≤ (H : ℝ) /
        (8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_left hHpos.le hden hsmall
    _ ≤ badIntervalCofactorSieveBase p₀ H k :=
      badIntervalCofactorSieveBase_ge hp₀ hk hcard

/-- After the stronger denominator absorption, the fixed-fiber cardinality
has exactly the paper's `H^(-0.9(k-1))` decay.  Degree two is intentionally
excluded; degrees two and three belong to the later large-`p₀` scale split. -/
theorem scaleNormalizedBadIntervalUnionAt_le_rpow_neg_nine_tenths_sub_one
    {x p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 3 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hsmall : 8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50)) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      16 * (badIntervalCofactorBudget x p₀ + 1) *
        (H : ℝ) ^ (-(9 : ℝ) / 10 * ((k : ℝ) - 1)) := by
  have hkOne : 1 ≤ k := by omega
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hbase := badIntervalCofactorSieveBase_ge_rpow_forty_seven_fiftieths
    hp₀ hH hkOne hcard hsmall
  have hweight : (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) ≤
      badIntervalCofactorSieveWeight p₀ H k :=
    pow_le_pow_left₀ (Real.rpow_nonneg hHpos.le _) hbase k
  have hweighted : (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
    calc
      (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        badIntervalCofactorSieveWeight p₀ H k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) := by
            gcongr
      _ ≤ (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
        simpa only [badIntervalCofactorSieveWeight,
          badIntervalCofactorSieveBase] using
          (scaleNormalizedBadIntervalUnionAt_mul_cofactorSourceWeight_le
            hH hHp₀ hkOne hkcard hproduct)
  have hpowPos : 0 < (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) := by
    positivity
  have hdiv : ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) /
        (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) :=
    (le_div_iff₀ hpowPos).2 (by simpa only [mul_comm] using hweighted)
  have hpowEq : (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) =
      (H : ℝ) ^ (((47 : ℝ) / 50) * (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le]
  have hHOne : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hexp : 1 - (47 : ℝ) / 50 * (k : ℝ) ≤
      -(9 : ℝ) / 10 * ((k : ℝ) - 1) := by
    have hkReal : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hratioEq : (H : ℝ) /
      (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) =
      (H : ℝ) ^ (1 - (47 : ℝ) / 50 * (k : ℝ)) := by
    calc
      (H : ℝ) / (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) =
          (H : ℝ) ^ (1 : ℝ) /
            (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) := by
        rw [Real.rpow_one]
      _ = (H : ℝ) ^ (1 - (47 : ℝ) / 50 * (k : ℝ)) :=
        (Real.rpow_sub hHpos 1 ((47 : ℝ) / 50 * (k : ℝ))).symm
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) /
          (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) := hdiv
    _ = 16 * (badIntervalCofactorBudget x p₀ + 1) *
        (H : ℝ) ^ (1 - (47 : ℝ) / 50 * (k : ℝ)) := by
      rw [hpowEq]
      calc
        (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) /
            (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) =
          16 * (badIntervalCofactorBudget x p₀ + 1) *
            ((H : ℝ) / (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ))) := by ring
        _ = _ := by rw [hratioEq]
    _ ≤ 16 * (badIntervalCofactorBudget x p₀ + 1) *
        (H : ℝ) ^ (-(9 : ℝ) / 10 * ((k : ℝ) - 1)) := by
      gcongr

/-- Uniform replacement for the preceding decay estimate down to degree two.
The slightly relaxed coefficient `22/25` exactly absorbs the leading `H` at
`k = 2` and retains ample room for a `z(x)⁻⁴` saddle. -/
theorem scaleNormalizedBadIntervalUnionAt_le_rpow_neg_twenty_two_twenty_fifths_sub_one
    {x p₀ H k : ℕ} (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hk : 2 ≤ k) (hkcard : 2 * k ≤ (badIntervalUpperPrimes p₀).card)
    (hproduct : ((2 * p₀) ^ k) * ((2 * p₀) ^ k) ≤
      badIntervalCofactorBudget x p₀ + 1)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hsmall : 8 * (k : ℝ) * Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50)) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      16 * (badIntervalCofactorBudget x p₀ + 1) *
        (H : ℝ) ^ (-(22 : ℝ) / 25 * ((k : ℝ) - 1)) := by
  have hkOne : 1 ≤ k := by omega
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hbase := badIntervalCofactorSieveBase_ge_rpow_forty_seven_fiftieths
    hp₀ hH hkOne hcard hsmall
  have hweight : (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) ≤
      badIntervalCofactorSieveWeight p₀ H k :=
    pow_le_pow_left₀ (Real.rpow_nonneg hHpos.le _) hbase k
  have hweighted : (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) *
        ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
    calc
      (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        badIntervalCofactorSieveWeight p₀ H k *
          ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) := by
            gcongr
      _ ≤ (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) := by
        simpa only [badIntervalCofactorSieveWeight,
          badIntervalCofactorSieveBase] using
          (scaleNormalizedBadIntervalUnionAt_mul_cofactorSourceWeight_le
            hH hHp₀ hkOne hkcard hproduct)
  have hpowPos : 0 < (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) := by
    positivity
  have hdiv : ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) /
        (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) :=
    (le_div_iff₀ hpowPos).2 (by simpa only [mul_comm] using hweighted)
  have hpowEq : (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) =
      (H : ℝ) ^ (((47 : ℝ) / 50) * (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hHpos.le]
  have hHOne : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hexp : 1 - (47 : ℝ) / 50 * (k : ℝ) ≤
      -(22 : ℝ) / 25 * ((k : ℝ) - 1) := by
    have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hratioEq : (H : ℝ) /
      (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) =
      (H : ℝ) ^ (1 - (47 : ℝ) / 50 * (k : ℝ)) := by
    calc
      (H : ℝ) / (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) =
          (H : ℝ) ^ (1 : ℝ) /
            (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) := by
        rw [Real.rpow_one]
      _ = (H : ℝ) ^ (1 - (47 : ℝ) / 50 * (k : ℝ)) :=
        (Real.rpow_sub hHpos 1 ((47 : ℝ) / 50 * (k : ℝ))).symm
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) /
          (((H : ℝ) ^ ((47 : ℝ) / 50)) ^ k) := hdiv
    _ = 16 * (badIntervalCofactorBudget x p₀ + 1) *
        (H : ℝ) ^ (1 - (47 : ℝ) / 50 * (k : ℝ)) := by
      rw [hpowEq]
      calc
        (H : ℝ) * (16 * (badIntervalCofactorBudget x p₀ + 1)) /
            (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ)) =
          16 * (badIntervalCofactorBudget x p₀ + 1) *
            ((H : ℝ) / (H : ℝ) ^ ((47 : ℝ) / 50 * (k : ℝ))) := by ring
        _ = _ := by rw [hratioEq]
    _ ≤ 16 * (badIntervalCofactorBudget x p₀ + 1) *
        (H : ℝ) ^ (-(22 : ℝ) / 25 * ((k : ℝ) - 1)) := by
      gcongr

/-- The valid `k ≥ 4` quarter-bound turns the preceding power decay into
the explicit exponential term used immediately before the saddle estimate. -/
theorem canonicalCofactorDegreeDecay_le_exp
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H)
    (hk : 4 ≤ badIntervalCofactorSieveDegree x p₀) :
    (H : ℝ) ^ (-(9 : ℝ) / 10 *
        ((badIntervalCofactorSieveDegree x p₀ : ℝ) - 1)) ≤
      Real.exp (-(9 : ℝ) / 40 *
        (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
          Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
  let k := badIntervalCofactorSieveDegree x p₀
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hHOne : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hHOne
  have hlogBase : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hdegree :=
    badIntervalCofactorSieveDegree_sub_one_gt_log_ratio_div_four hx hp₀ hk
  have hneg : -(9 : ℝ) / 10 * ((k : ℝ) - 1) ≤
      -(9 : ℝ) / 10 *
        (Real.log (((2 * x : ℕ) : ℝ)) /
          (4 * Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
    nlinarith
  have hexp : Real.log (H : ℝ) *
        (-(9 : ℝ) / 10 * ((k : ℝ) - 1)) ≤
      -(9 : ℝ) / 40 *
        (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
          Real.log (((2 * p₀ : ℕ) : ℝ))) := by
    calc
      Real.log (H : ℝ) * (-(9 : ℝ) / 10 * ((k : ℝ) - 1)) ≤
          Real.log (H : ℝ) * (-(9 : ℝ) / 10 *
            (Real.log (((2 * x : ℕ) : ℝ)) /
              (4 * Real.log (((2 * p₀ : ℕ) : ℝ))))) :=
        mul_le_mul_of_nonneg_left hneg hlogH
      _ = -(9 : ℝ) / 40 *
          (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
            Real.log (((2 * p₀ : ℕ) : ℝ))) := by
        field_simp [ne_of_gt hlogBase]
        ring
  rw [Real.rpow_def_of_pos hHpos]
  exact Real.exp_le_exp.mpr hexp

/-- Degree-two-safe exponential conversion using the corrected eighth-bound.
Its coefficient `11/100` is still strong enough for a `z(x)⁻⁴` saddle. -/
theorem canonicalCofactorDegreeDecay_le_exp_of_two
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀) (hH : 1 ≤ H)
    (hk : 2 ≤ badIntervalCofactorSieveDegree x p₀) :
    (H : ℝ) ^ (-(22 : ℝ) / 25 *
        ((badIntervalCofactorSieveDegree x p₀ : ℝ) - 1)) ≤
      Real.exp (-(11 : ℝ) / 100 *
        (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
          Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
  let k := badIntervalCofactorSieveDegree x p₀
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hHOne : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hlogH : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg hHOne
  have hlogBase : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hdegree :=
    badIntervalCofactorSieveDegree_sub_one_gt_log_ratio_div_eight hx hp₀ hk
  have hneg : -(22 : ℝ) / 25 * ((k : ℝ) - 1) ≤
      -(22 : ℝ) / 25 *
        (Real.log (((2 * x : ℕ) : ℝ)) /
          (8 * Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
    nlinarith
  have hexp : Real.log (H : ℝ) *
        (-(22 : ℝ) / 25 * ((k : ℝ) - 1)) ≤
      -(11 : ℝ) / 100 *
        (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
          Real.log (((2 * p₀ : ℕ) : ℝ))) := by
    calc
      Real.log (H : ℝ) * (-(22 : ℝ) / 25 * ((k : ℝ) - 1)) ≤
          Real.log (H : ℝ) * (-(22 : ℝ) / 25 *
            (Real.log (((2 * x : ℕ) : ℝ)) /
              (8 * Real.log (((2 * p₀ : ℕ) : ℝ))))) :=
        mul_le_mul_of_nonneg_left hneg hlogH
      _ = -(11 : ℝ) / 100 *
          (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
            Real.log (((2 * p₀ : ℕ) : ℝ))) := by
        field_simp [ne_of_gt hlogBase]
        ring
  rw [Real.rpow_def_of_pos hHpos]
  exact Real.exp_le_exp.mpr hexp

/-- Canonical fixed-fiber estimate after the degree lower bound has been
inserted, but before optimizing in `p₀` and summing the scale fibers. -/
theorem scaleNormalizedBadIntervalUnionAt_le_canonicalDegreeExp
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ))
    (hdegree : 4 ≤ badIntervalCofactorSieveDegree x p₀)
    (hsmall : 8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50)) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      16 * (badIntervalCofactorBudget x p₀ + 1) *
        Real.exp (-(9 : ℝ) / 40 *
          (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
            Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
  have hkcard := two_mul_badIntervalCofactorSieveDegree_le_card
    hp₀ hcard hlarge
  have hproduct :=
    badIntervalCofactorSieveDegree_product_le (x := x) hp₀
  have hfiber :=
    scaleNormalizedBadIntervalUnionAt_le_rpow_neg_nine_tenths_sub_one
      hp₀ hH hHp₀ (by omega : 3 ≤ badIntervalCofactorSieveDegree x p₀)
      hkcard hproduct hcard hsmall
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        16 * (badIntervalCofactorBudget x p₀ + 1) *
          (H : ℝ) ^ (-(9 : ℝ) / 10 *
            ((badIntervalCofactorSieveDegree x p₀ : ℝ) - 1)) := hfiber
    _ ≤ 16 * (badIntervalCofactorBudget x p₀ + 1) *
        Real.exp (-(9 : ℝ) / 40 *
          (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
            Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
      gcongr
      exact canonicalCofactorDegreeDecay_le_exp hx hp₀ hH hdegree

/-- Degree-two-safe canonical exponential fixed-fiber estimate. -/
theorem scaleNormalizedBadIntervalUnionAt_le_canonicalDegreeExp_of_two
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hH : 1 ≤ H) (hHp₀ : H < p₀)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ))
    (hdegree : 2 ≤ badIntervalCofactorSieveDegree x p₀)
    (hsmall : 8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50)) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      16 * (badIntervalCofactorBudget x p₀ + 1) *
        Real.exp (-(11 : ℝ) / 100 *
          (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
            Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
  have hkcard := two_mul_badIntervalCofactorSieveDegree_le_card
    hp₀ hcard hlarge
  have hproduct :=
    badIntervalCofactorSieveDegree_product_le (x := x) hp₀
  have hfiber :=
    scaleNormalizedBadIntervalUnionAt_le_rpow_neg_twenty_two_twenty_fifths_sub_one
      hp₀ hH hHp₀ hdegree hkcard hproduct hcard hsmall
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        16 * (badIntervalCofactorBudget x p₀ + 1) *
          (H : ℝ) ^ (-(22 : ℝ) / 25 *
            ((badIntervalCofactorSieveDegree x p₀ : ℝ) - 1)) := hfiber
    _ ≤ 16 * (badIntervalCofactorBudget x p₀ + 1) *
        Real.exp (-(11 : ℝ) / 100 *
          (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
            Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
      gcongr
      exact canonicalCofactorDegreeDecay_le_exp_of_two hx hp₀ hH hdegree

/-- Source-facing version in which the long-interval hypothesis itself
discharges the denominator absorption.  The remaining side conditions expose
exactly the prime-scale split and PNT range still needed by the fiber sum. -/
theorem eventually_scaleNormalizedBadIntervalUnionAt_le_canonicalDegreeExp_of_long :
    ∀ᶠ x : ℕ in atTop, ∀ {p₀ H : ℕ},
      1 ≤ p₀ → 1 ≤ H → H < p₀ →
      taoTypicalLengthCutoff x ≤ H →
      ((2 * p₀ : ℕ) : ℝ) /
          (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
        ((badIntervalUpperPrimes p₀).card : ℝ) →
      4 * Real.log
          ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
        ((2 * p₀ : ℕ) : ℝ) →
      4 ≤ badIntervalCofactorSieveDegree x p₀ →
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        16 * (badIntervalCofactorBudget x p₀ + 1) *
          Real.exp (-(9 : ℝ) / 40 *
            (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
              Real.log (((2 * p₀ : ℕ) : ℝ)))) := by
  filter_upwards [eventually_canonicalCofactorDenominator_le_of_long,
    eventually_ge_atTop (1 : ℕ)] with x hden hx
  intro p₀ H hp₀ hH hHp₀ hlong hcard hlarge hdegree
  exact scaleNormalizedBadIntervalUnionAt_le_canonicalDegreeExp
    hx hp₀ hH hHp₀ hcard hlarge hdegree (hden hp₀ hlong)

end

end Tao2026
