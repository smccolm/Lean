import Tao2026.BadIntervalLongSum

/-!
# Short normalized intervals with a large distinguished prime

This module treats the elementary large-`p₀` branch adjacent to the long
large-sieve argument.  Once condition (i) holds, the unsieved cofactor cover
can be summed using a reciprocal-square tail.
-/

namespace Tao2026

open Filter

noncomputable section

/-- First integer strictly above the real source boundary `x^(3/20)`. -/
def badIntervalLargePrimeTailCutoff (x : ℕ) : ℕ :=
  ⌊(x : ℝ) ^ ((3 : ℝ) / 20)⌋₊ + 1

/-- Natural ceiling encoding of Tao's preliminary range `H < x^0.14`. -/
def badIntervalLargePrimeLengthCutoff (x : ℕ) : ℕ :=
  ⌈(x : ℝ) ^ ((7 : ℝ) / 50)⌉₊

/-- Dyadic exponents sufficient for every power-of-two length below Tao's
preliminary `x^0.14` cutoff. -/
def badIntervalShortDyadicExponents (x : ℕ) : Finset ℕ :=
  Finset.range (Nat.log 2 (badIntervalLargePrimeLengthCutoff x) + 1)

/-- Distinguished primes in the complementary range `p₀^20 > x^3` which
can occur in a nonempty comparable-scale normalized fiber. -/
def badIntervalShortLargePrimes (x : ℕ) : Finset ℕ :=
  (Finset.Icc (badIntervalLargePrimeTailCutoff x) x).filter fun p₀ =>
    p₀ ^ 2 ≤ 2 * x ∧ x ^ 3 < p₀ ^ 20

/-- Parameter pairs in the short, large-distinguished-prime branch. -/
def badIntervalShortLargePrimeFiberIndices (x : ℕ) : Finset (ℕ × ℕ) :=
  ((badIntervalShortLargePrimes x).product
      (badIntervalShortDyadicExponents x)).filter fun pr =>
    2 ^ pr.2 < badIntervalLargePrimeLengthCutoff x ∧ 2 ^ pr.2 < pr.1

/-- Explicit union of all fixed fibers in the short large-prime branch. -/
def badIntervalShortLargePrimeFiberUnion (x : ℕ) : Finset ℕ :=
  (badIntervalShortLargePrimeFiberIndices x).biUnion fun pr =>
    scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)

/-- Actual comparable-scale normalized intervals which are short and whose
named distinguished prime is above `x^(3/20)`. -/
noncomputable def taoShortLargePrimeFailureIndices (x : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).filter fun NH =>
    NH.2 < badIntervalLargePrimeLengthCutoff x ∧
      ∃ p₀ k m : ℕ,
        IsNormalizedBadInterval NH.1 NH.2 p₀ k m ∧ x ^ 3 < p₀ ^ 20

/-- Union of the actual short large-prime normalized intervals. -/
noncomputable def taoShortLargePrimeFailureUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (taoShortLargePrimeFailureIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem mem_badIntervalShortLargePrimes {x p₀ : ℕ} :
    p₀ ∈ badIntervalShortLargePrimes x ↔
      badIntervalLargePrimeTailCutoff x ≤ p₀ ∧ p₀ ≤ x ∧
        p₀ ^ 2 ≤ 2 * x ∧ x ^ 3 < p₀ ^ 20 := by
  simp [badIntervalShortLargePrimes, and_assoc]

theorem mem_badIntervalShortLargePrimeFiberIndices {x p₀ r : ℕ} :
    (p₀, r) ∈ badIntervalShortLargePrimeFiberIndices x ↔
      p₀ ∈ badIntervalShortLargePrimes x ∧
        r ∈ badIntervalShortDyadicExponents x ∧
        2 ^ r < badIntervalLargePrimeLengthCutoff x ∧ 2 ^ r < p₀ := by
  simp [badIntervalShortLargePrimeFiberIndices, and_assoc]

theorem mem_taoShortLargePrimeFailureIndices {x N H : ℕ} :
    (N, H) ∈ taoShortLargePrimeFailureIndices x ↔
      (N, H) ∈ scaleNormalizedBadIntervalIndices x ∧
        H < badIntervalLargePrimeLengthCutoff x ∧
        ∃ p₀ k m : ℕ,
          IsNormalizedBadInterval N H p₀ k m ∧ x ^ 3 < p₀ ^ 20 := by
  classical
  simp [taoShortLargePrimeFailureIndices]

/-- The exact natural-power source inequality places `p₀` beyond the
floor-rounded real boundary. -/
theorem badIntervalLargePrimeTailCutoff_le_of_pow
    {x p₀ : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hpow : x ^ 3 < p₀ ^ 20) :
    badIntervalLargePrimeTailCutoff x ≤ p₀ := by
  have hxPos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hx)
  have hpPos : (0 : ℝ) < (p₀ : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hp₀)
  have hpowReal : (x : ℝ) ^ (3 : ℕ) < (p₀ : ℝ) ^ (20 : ℕ) := by
    exact_mod_cast hpow
  have hrootPower := Real.rpow_lt_rpow
    (show 0 ≤ (x : ℝ) ^ (3 : ℕ) by positivity) hpowReal
    (show (0 : ℝ) < 1 / 20 by norm_num)
  have hroot : (x : ℝ) ^ ((3 : ℝ) / 20) < (p₀ : ℝ) := by
    calc
      (x : ℝ) ^ ((3 : ℝ) / 20) =
          ((x : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 20) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxPos.le]
        norm_num
      _ < ((p₀ : ℝ) ^ (20 : ℕ)) ^ ((1 : ℝ) / 20) := hrootPower
      _ = (p₀ : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hpPos.le]
        norm_num
  have hfloorCast :
      ((⌊(x : ℝ) ^ ((3 : ℝ) / 20)⌋₊ : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((3 : ℝ) / 20) := by
    exact Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hfloorLt : ⌊(x : ℝ) ^ ((3 : ℝ) / 20)⌋₊ < p₀ := by
    exact_mod_cast hfloorCast.trans_lt hroot
  simpa only [badIntervalLargePrimeTailCutoff] using hfloorLt

/-- The natural-power encoding `H^50 < x^7` of Tao's `H < x^0.14`
condition lies inside the ceiling-rounded finite length range. -/
theorem lt_badIntervalLargePrimeLengthCutoff_of_pow
    {x H : ℕ} (hx : 1 ≤ x) (hpow : H ^ 50 < x ^ 7) :
    H < badIntervalLargePrimeLengthCutoff x := by
  have hxPos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hx)
  have hpowReal : (H : ℝ) ^ (50 : ℕ) < (x : ℝ) ^ (7 : ℕ) := by
    exact_mod_cast hpow
  have hrootPower := Real.rpow_lt_rpow
    (show 0 ≤ (H : ℝ) ^ (50 : ℕ) by positivity) hpowReal
    (show (0 : ℝ) < 1 / 50 by norm_num)
  have hroot : (H : ℝ) < (x : ℝ) ^ ((7 : ℝ) / 50) := by
    calc
      (H : ℝ) = ((H : ℝ) ^ (50 : ℕ)) ^ ((1 : ℝ) / 50) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      _ < ((x : ℝ) ^ (7 : ℕ)) ^ ((1 : ℝ) / 50) := hrootPower
      _ = (x : ℝ) ^ ((7 : ℝ) / 50) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hxPos.le]
        norm_num
  have hceil : (x : ℝ) ^ ((7 : ℝ) / 50) ≤
      (badIntervalLargePrimeLengthCutoff x : ℝ) := by
    exact Nat.le_ceil _
  exact_mod_cast hroot.trans_le hceil

/-- The unsieved cofactor cover gives the expected reciprocal-square bound
for every nonvacuous fixed fiber. -/
theorem card_scaleNormalizedBadIntervalUnionAt_cast_le_largePrime
    {x p₀ H : ℕ} (hp₀ : 1 ≤ p₀) (hpSq : p₀ ^ 2 ≤ 2 * x) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      8 * (H : ℝ) * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
  have hcard := card_scaleNormalizedBadIntervalUnionAt_le_two_mul_budget
    x p₀ H
  have hcardReal :
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        ((2 * H * (badIntervalCofactorBudget x p₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hbudget := cast_badIntervalCofactorBudget_add_one_le hp₀ hpSq
  have hbudget' : (badIntervalCofactorBudget x p₀ : ℝ) + 1 ≤
      4 * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbudget
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        ((2 * H * (badIntervalCofactorBudget x p₀ + 1) : ℕ) : ℝ) := hcardReal
    _ = 2 * (H : ℝ) * ((badIntervalCofactorBudget x p₀ : ℝ) + 1) := by
      push_cast
      ring
    _ ≤ 2 * (H : ℝ) * (4 * (x : ℝ) / (p₀ : ℝ) ^ 2) := by
      gcongr
    _ = 8 * (H : ℝ) * (x : ℝ) / (p₀ : ℝ) ^ 2 := by ring

theorem sum_range_two_pow (n : ℕ) :
    (∑ r ∈ Finset.range n, 2 ^ r) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpowPos : 0 < 2 ^ n := pow_pos (by norm_num) n
      omega

/-- The total of all dyadic lengths below the short cutoff is at most twice
that cutoff. -/
theorem sum_badIntervalShortDyadicExponents_pow_le
    {x : ℕ} (hcutoff : 0 < badIntervalLargePrimeLengthCutoff x) :
    (∑ r ∈ badIntervalShortDyadicExponents x, (2 ^ r : ℝ)) ≤
      2 * (badIntervalLargePrimeLengthCutoff x : ℝ) := by
  have hpowLog :
      2 ^ Nat.log 2 (badIntervalLargePrimeLengthCutoff x) ≤
        badIntervalLargePrimeLengthCutoff x :=
    Nat.pow_log_le_self 2 hcutoff.ne'
  have hsumNat :
      (∑ r ∈ badIntervalShortDyadicExponents x, 2 ^ r) ≤
        2 * badIntervalLargePrimeLengthCutoff x := by
    rw [badIntervalShortDyadicExponents, sum_range_two_pow, pow_succ]
    omega
  exact_mod_cast hsumNat

/-- Cardinality of the explicit fiber union is bounded by the sum of the
reciprocal-square fixed-fiber estimates. -/
theorem card_badIntervalShortLargePrimeFiberUnion_cast_le_sum (x : ℕ) :
    ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
      ∑ p₀ ∈ badIntervalShortLargePrimes x,
        ∑ r ∈ badIntervalShortDyadicExponents x,
          8 * (2 ^ r : ℝ) * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
  classical
  have hunionNat : (badIntervalShortLargePrimeFiberUnion x).card ≤
      ∑ pr ∈ badIntervalShortLargePrimeFiberIndices x,
        (scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)).card :=
    Finset.card_biUnion_le
  have hunion : ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
      ∑ pr ∈ badIntervalShortLargePrimeFiberIndices x,
        ((scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)).card : ℝ) := by
    exact_mod_cast hunionNat
  calc
    ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
        ∑ pr ∈ badIntervalShortLargePrimeFiberIndices x,
          ((scaleNormalizedBadIntervalUnionAt x pr.1 (2 ^ pr.2)).card : ℝ) :=
      hunion
    _ ≤ ∑ pr ∈ badIntervalShortLargePrimeFiberIndices x,
          8 * (2 ^ pr.2 : ℝ) * (x : ℝ) / (pr.1 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro pr hpr
      have hdata := mem_badIntervalShortLargePrimeFiberIndices.mp hpr
      have hpData := mem_badIntervalShortLargePrimes.mp hdata.1
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        (card_scaleNormalizedBadIntervalUnionAt_cast_le_largePrime
          (H := 2 ^ pr.2)
          ((show 1 ≤ badIntervalLargePrimeTailCutoff x by
            simp [badIntervalLargePrimeTailCutoff]).trans hpData.1)
          hpData.2.2.1)
    _ ≤ ∑ pr ∈ (badIntervalShortLargePrimes x).product
          (badIntervalShortDyadicExponents x),
          8 * (2 ^ pr.2 : ℝ) * (x : ℝ) / (pr.1 : ℝ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun pr _hpr _hnot => by positivity)
    _ = ∑ p₀ ∈ badIntervalShortLargePrimes x,
          ∑ r ∈ badIntervalShortDyadicExponents x,
            8 * (2 ^ r : ℝ) * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
      simpa using (Finset.sum_product'
        (badIntervalShortLargePrimes x)
        (badIntervalShortDyadicExponents x)
        (fun p₀ r => 8 * (2 ^ r : ℝ) * (x : ℝ) / (p₀ : ℝ) ^ 2))

/-- Closed finite bound after summing both the dyadic lengths and the
large-prime reciprocal-square tail. -/
theorem card_badIntervalShortLargePrimeFiberUnion_cast_le_source
    {x : ℕ} (hcutoff : 0 < badIntervalLargePrimeLengthCutoff x)
    (htail : 2 ≤ badIntervalLargePrimeTailCutoff x) :
    ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
      16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ) /
        ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ) := by
  classical
  have hsum := card_badIntervalShortLargePrimeFiberUnion_cast_le_sum x
  have hlength := sum_badIntervalShortDyadicExponents_pow_le hcutoff
  have hpSubset : badIntervalShortLargePrimes x ⊆
      Finset.Icc (badIntervalLargePrimeTailCutoff x) x :=
    Finset.filter_subset _ _
  calc
    ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
        ∑ p₀ ∈ badIntervalShortLargePrimes x,
          ∑ r ∈ badIntervalShortDyadicExponents x,
            8 * (2 ^ r : ℝ) * (x : ℝ) / (p₀ : ℝ) ^ 2 := hsum
    _ = ∑ p₀ ∈ badIntervalShortLargePrimes x,
          (8 * (x : ℝ) / (p₀ : ℝ) ^ 2) *
            (∑ r ∈ badIntervalShortDyadicExponents x, (2 ^ r : ℝ)) := by
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ p₀ ∈ badIntervalShortLargePrimes x,
          (8 * (x : ℝ) / (p₀ : ℝ) ^ 2) *
            (2 * (badIntervalLargePrimeLengthCutoff x : ℝ)) := by
      apply Finset.sum_le_sum
      intro p₀ hp₀
      gcongr
    _ = ∑ p₀ ∈ badIntervalShortLargePrimes x,
          (16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ)) *
            (1 / (p₀ : ℝ) ^ 2) := by
      apply Finset.sum_congr rfl
      intro p₀ hp₀
      ring
    _ ≤ ∑ p₀ ∈ Finset.Icc (badIntervalLargePrimeTailCutoff x) x,
          (16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ)) *
            (1 / (p₀ : ℝ) ^ 2) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hpSubset
        (fun p₀ _hp _hnot => by positivity)
    _ = (16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ)) *
          (∑ p₀ ∈ Finset.Icc (badIntervalLargePrimeTailCutoff x) x,
            (1 : ℝ) / (p₀ : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ (16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ)) *
          (1 / ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ)) := by
      gcongr
      exact sum_Icc_one_div_nat_sq_le htail
    _ = 16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ) /
          ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ) := by ring

/-- Eventual floor and logarithmic comparisons needed to turn the finite
source bound into a fixed power saving. -/
theorem eventually_badIntervalLargePrimeTail_data :
    ∀ᶠ x : ℕ in atTop,
      0 < badIntervalLargePrimeLengthCutoff x ∧
      2 ≤ badIntervalLargePrimeTailCutoff x ∧
      (x : ℝ) ^ ((3 : ℝ) / 20) / 2 ≤
        ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ) ∧
      32 * (badIntervalLargePrimeLengthCutoff x : ℝ) ≤
        (x : ℝ) ^ ((29 : ℝ) / 200) := by
  have htailGrowth : Tendsto
      (fun x : ℕ => (x : ℝ) ^ ((3 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp
      tendsto_natCast_atTop_atTop
  have hlengthGrowth : Tendsto
      (fun x : ℕ => (x : ℝ) ^ ((7 : ℝ) / 50)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 50)).comp
      tendsto_natCast_atTop_atTop
  have habsorbGrowth : Tendsto
      (fun x : ℕ => (x : ℝ) ^ ((1 : ℝ) / 200)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards
    [htailGrowth.eventually (eventually_ge_atTop (2 : ℝ)),
      hlengthGrowth.eventually (eventually_ge_atTop (1 : ℝ)),
      habsorbGrowth.eventually (eventually_ge_atTop (64 : ℝ))]
      with x htailTwo hlengthOne habsorbLarge
  have hxPos : (0 : ℝ) < (x : ℝ) := by
    have hxNatPos : 0 < x := by
      by_contra hx
      have hxZero : x = 0 := Nat.eq_zero_of_not_pos hx
      norm_num [hxZero] at hlengthOne
    exact_mod_cast hxNatPos
  have hlengthNonneg : 0 ≤ (x : ℝ) ^ ((7 : ℝ) / 50) := by positivity
  have hcutoffSpec : (x : ℝ) ^ ((7 : ℝ) / 50) ≤
      (badIntervalLargePrimeLengthCutoff x : ℝ) := by
    exact Nat.le_ceil _
  have hcutoffPos : 0 < badIntervalLargePrimeLengthCutoff x := by
    have : (1 : ℝ) ≤ (badIntervalLargePrimeLengthCutoff x : ℝ) :=
      hlengthOne.trans hcutoffSpec
    exact_mod_cast this
  let y : ℝ := (x : ℝ) ^ ((3 : ℝ) / 20)
  have hyNonneg : 0 ≤ y := by dsimp only [y]; positivity
  have hfloorOne : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by
    dsimp only [y]
    linarith)
  have htailTwoNat : 2 ≤ badIntervalLargePrimeTailCutoff x := by
    dsimp only [badIntervalLargePrimeTailCutoff]
    change 2 ≤ ⌊y⌋₊ + 1
    omega
  have hfloorUpper : y < (⌊y⌋₊ : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one y
  have hden : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
    dsimp only [y] at htailTwo ⊢
    linarith
  have hden' : (x : ℝ) ^ ((3 : ℝ) / 20) / 2 ≤
      ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ) := by
    simpa only [badIntervalLargePrimeTailCutoff, Nat.add_sub_cancel] using hden
  have hcutoffUpper : (badIntervalLargePrimeLengthCutoff x : ℝ) <
      (x : ℝ) ^ ((7 : ℝ) / 50) + 1 := by
    simpa only [badIntervalLargePrimeLengthCutoff] using
      Nat.ceil_lt_add_one hlengthNonneg
  have htwice : (badIntervalLargePrimeLengthCutoff x : ℝ) ≤
      2 * (x : ℝ) ^ ((7 : ℝ) / 50) := by linarith
  have habsorbProduct :
      64 * (x : ℝ) ^ ((7 : ℝ) / 50) ≤
        (x : ℝ) ^ ((7 : ℝ) / 50) * (x : ℝ) ^ ((1 : ℝ) / 200) := by
    rw [mul_comm 64]
    exact mul_le_mul_of_nonneg_left habsorbLarge hlengthNonneg
  have hpowerIdentity :
      (x : ℝ) ^ ((7 : ℝ) / 50) * (x : ℝ) ^ ((1 : ℝ) / 200) =
        (x : ℝ) ^ ((29 : ℝ) / 200) := by
    rw [← Real.rpow_add hxPos]
    congr 1
    norm_num
  have habsorb : 32 * (badIntervalLargePrimeLengthCutoff x : ℝ) ≤
      (x : ℝ) ^ ((29 : ℝ) / 200) := by
    calc
      32 * (badIntervalLargePrimeLengthCutoff x : ℝ) ≤
          64 * (x : ℝ) ^ ((7 : ℝ) / 50) := by nlinarith
      _ ≤ (x : ℝ) ^ ((7 : ℝ) / 50) *
          (x : ℝ) ^ ((1 : ℝ) / 200) := habsorbProduct
      _ = (x : ℝ) ^ ((29 : ℝ) / 200) := hpowerIdentity
  exact ⟨hcutoffPos, htailTwoNat, hden', habsorb⟩

/-- The complete explicit short large-prime fiber union has a fixed
`x^(199/200)` power saving. -/
theorem eventually_card_badIntervalShortLargePrimeFiberUnion_cast_le :
    ∀ᶠ x : ℕ in atTop,
      ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
        (x : ℝ) ^ ((199 : ℝ) / 200) := by
  filter_upwards [eventually_badIntervalLargePrimeTail_data]
      with x hdata
  obtain ⟨hcutoff, htail, hden, habsorb⟩ := hdata
  have hsource := card_badIntervalShortLargePrimeFiberUnion_cast_le_source
    hcutoff htail
  have hxPos : (0 : ℝ) < (x : ℝ) := by
    have hxNatPos : 0 < x := by
      by_contra hx
      have hxZero : x = 0 := Nat.eq_zero_of_not_pos hx
      norm_num [hxZero, badIntervalLargePrimeTailCutoff] at htail
    exact_mod_cast hxNatPos
  have hdenPos : (0 : ℝ) <
      ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < badIntervalLargePrimeTailCutoff x - 1)
  have hrpowTailPos : 0 < (x : ℝ) ^ ((3 : ℝ) / 20) :=
    Real.rpow_pos_of_pos hxPos _
  calc
    ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) ≤
        16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ) /
          ((badIntervalLargePrimeTailCutoff x - 1 : ℕ) : ℝ) := hsource
    _ ≤ 16 * (badIntervalLargePrimeLengthCutoff x : ℝ) * (x : ℝ) /
          ((x : ℝ) ^ ((3 : ℝ) / 20) / 2) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (32 * (badIntervalLargePrimeLengthCutoff x : ℝ)) * (x : ℝ) /
          (x : ℝ) ^ ((3 : ℝ) / 20) := by field_simp; ring
    _ ≤ (x : ℝ) ^ ((29 : ℝ) / 200) * (x : ℝ) /
          (x : ℝ) ^ ((3 : ℝ) / 20) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right habsorb hxPos.le)
        hrpowTailPos.le
    _ = (x : ℝ) ^ (((29 : ℝ) / 200 + 1) - (3 : ℝ) / 20) := by
      rw [Real.rpow_sub hxPos, Real.rpow_add hxPos, Real.rpow_one]
    _ = (x : ℝ) ^ ((199 : ℝ) / 200) := by norm_num

/-- Every actual interval in this branch occurs in the explicit fixed-fiber
union. -/
theorem taoShortLargePrimeFailureUnion_subset_fiberUnion
    {x : ℕ} (hx : 2 ≤ x) :
    taoShortLargePrimeFailureUnion x ⊆
      badIntervalShortLargePrimeFiberUnion x := by
  classical
  intro n hn
  obtain ⟨⟨N, H⟩, hNH, hnInterval⟩ := Finset.mem_biUnion.mp hn
  rw [mem_taoShortLargePrimeFailureIndices] at hNH
  obtain ⟨hscale, hshort, p₀, k, m, hnorm, hpRange⟩ := hNH
  have hscaleData := mem_scaleNormalizedBadIntervalIndices.mp hscale
  obtain ⟨p', k', m', hnorm', hleft, hright⟩ := hscaleData.2.2
  have hstart : N ∈ scaleNormalizedBadIntervalStartsAt x p₀ H := by
    exact mem_scaleNormalizedBadIntervalStartsAt.mpr
      ⟨hscaleData.1, k, m, hnorm, hleft, hright⟩
  have hpSq : p₀ ^ 2 ≤ 2 * x :=
    p₀_sq_le_two_mul_x_of_mem_scaleNormalizedBadIntervalStartsAt hstart
  obtain ⟨_hHTwo, _hbad, hpPrime, hHltp, _hpMax, _hk, _hm,
      _hkm, _hendpoint, r, hr⟩ := hnorm
  have hpLeX : p₀ ≤ x := by
    nlinarith [sq_nonneg (p₀ - x)]
  have hpCutoff : badIntervalLargePrimeTailCutoff x ≤ p₀ :=
    badIntervalLargePrimeTailCutoff_le_of_pow
      (by omega) hpPrime.one_le hpRange
  have hpMem : p₀ ∈ badIntervalShortLargePrimes x := by
    exact mem_badIntervalShortLargePrimes.mpr
      ⟨hpCutoff, hpLeX, hpSq, hpRange⟩
  have hrPowLe : 2 ^ r ≤ badIntervalLargePrimeLengthCutoff x := by
    simpa [← hr] using Nat.le_of_lt hshort
  have hrLog : r ≤ Nat.log 2 (badIntervalLargePrimeLengthCutoff x) :=
    Nat.le_log_of_pow_le (by norm_num) hrPowLe
  have hrMem : r ∈ badIntervalShortDyadicExponents x := by
    simp [badIntervalShortDyadicExponents, hrLog]
  have hpr : (p₀, r) ∈ badIntervalShortLargePrimeFiberIndices x := by
    exact mem_badIntervalShortLargePrimeFiberIndices.mpr
      ⟨hpMem, hrMem, by simpa [← hr] using hshort,
        by simpa [← hr] using hHltp⟩
  refine Finset.mem_biUnion.mpr ⟨(p₀, r), hpr, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨N, ?_, ?_⟩
  · simpa [← hr] using hstart
  · simpa [← hr] using hnInterval

theorem card_taoShortLargePrimeFailureUnion_le
    {x : ℕ} (hx : 2 ≤ x) :
    (taoShortLargePrimeFailureUnion x).card ≤
      (badIntervalShortLargePrimeFiberUnion x).card :=
  Finset.card_le_card
    (taoShortLargePrimeFailureUnion_subset_fiberUnion hx)

/-- Final fixed-power estimate for the actual preliminary large-`p₀`
failure branch in Proposition 6.5. -/
theorem eventually_card_taoShortLargePrimeFailureUnion_cast_le :
    ∀ᶠ x : ℕ in atTop,
      ((taoShortLargePrimeFailureUnion x).card : ℝ) ≤
        (x : ℝ) ^ ((199 : ℝ) / 200) := by
  filter_upwards
    [eventually_card_badIntervalShortLargePrimeFiberUnion_cast_le,
      eventually_ge_atTop (2 : ℕ)] with x hbound hx
  have hcard : ((taoShortLargePrimeFailureUnion x).card : ℝ) ≤
      ((badIntervalShortLargePrimeFiberUnion x).card : ℝ) := by
    exact_mod_cast card_taoShortLargePrimeFailureUnion_le hx
  exact hcard.trans hbound

end

end Tao2026
