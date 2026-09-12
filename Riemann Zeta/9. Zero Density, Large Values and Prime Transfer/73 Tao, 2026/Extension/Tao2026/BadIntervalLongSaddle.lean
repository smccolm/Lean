import Tao2026.BadIntervalLongOptimization

/-!
# Saddle optimization for long bad intervals

This module continues the source-faithful condition-(i) estimate from the
canonical-degree exponential fiber bound to Tao's arithmetic--geometric mean
saddle.  All constants and floor losses remain explicit.
-/

namespace Tao2026

open Filter

noncomputable section

/-- The positive numerator in the long-interval saddle exponent. -/
def badIntervalLongSaddleNumerator (x H : ℕ) : ℝ :=
  (9 : ℝ) / 40 * Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ)

/-- The degree-two-safe saddle numerator obtained from the corrected
eighth-comparison. -/
def badIntervalLongSaddleNumeratorOfTwo (x H : ℕ) : ℝ :=
  (11 : ℝ) / 100 * Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ)

/-- The literal long-interval cutoff supplies more than the amount of
`log x · log₂ x` needed for the final `z(x)⁻⁶` saving. -/
theorem badIntervalLongSaddleNumerator_ge
    {x H : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    (9 : ℝ) / 2 * Real.log (x : ℝ) * iteratedLog x ≤
      badIntervalLongSaddleNumerator x H := by
  have hlogPos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hxNat : 1 ≤ x := by
    by_contra hx
    have hxZero : x = 0 := by omega
    subst x
    norm_num at hlog
  have hxPos : 0 < (x : ℝ) := by
    exact_mod_cast hxNat
  have hiterNonneg : 0 ≤ iteratedLog x := by
    rw [iteratedLog]
    exact Real.log_nonneg hlog
  have htwoPos : 0 < (((2 * x : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < 2 * x)
  have hxTwo : (x : ℝ) ≤ (((2 * x : ℕ) : ℝ)) := by
    push_cast
    linarith
  have hlogTwo : Real.log (x : ℝ) ≤ Real.log (((2 * x : ℕ) : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hxPos)
      (by simpa only [Set.mem_Ioi] using htwoPos) hxTwo
  have hcut := taoTypicalLengthCutoff_spec x
  have hpowToH : (Real.log (x : ℝ)) ^ (20 : ℕ) ≤ (H : ℝ) :=
    hcut.trans (by exact_mod_cast hlong)
  have hpowPos : 0 < (Real.log (x : ℝ)) ^ (20 : ℕ) := pow_pos hlogPos _
  have hHPos : 0 < (H : ℝ) := hpowPos.trans_le hpowToH
  have hlogH : 20 * iteratedLog x ≤ Real.log (H : ℝ) := by
    calc
      20 * iteratedLog x =
          Real.log ((Real.log (x : ℝ)) ^ (20 : ℕ)) := by
        rw [Real.log_pow]
        norm_num [iteratedLog]
      _ ≤ Real.log (H : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (by simpa only [Set.mem_Ioi] using hpowPos)
          (by simpa only [Set.mem_Ioi] using hHPos) hpowToH
  have hprod :
      Real.log (x : ℝ) * (20 * iteratedLog x) ≤
        Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) := by
    exact mul_le_mul hlogTwo hlogH (by positivity)
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * x)))
  dsimp only [badIntervalLongSaddleNumerator]
  nlinarith [mul_nonneg hlogPos.le hiterNonneg]

theorem badIntervalLongSaddleNumeratorOfTwo_ge
    {x H : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    (11 : ℝ) / 5 * Real.log (x : ℝ) * iteratedLog x ≤
      badIntervalLongSaddleNumeratorOfTwo x H := by
  have hstrong := badIntervalLongSaddleNumerator_ge hlog hlong
  dsimp only [badIntervalLongSaddleNumerator,
    badIntervalLongSaddleNumeratorOfTwo] at hstrong ⊢
  nlinarith

/-- Six copies of Tao's `z`-exponent fit exactly inside the lower bound for
the long-interval saddle exponent. -/
theorem six_mul_log_taoZ_le_two_mul_sqrt_saddle
    {x H : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    6 * Real.log (taoZ x) ≤
      2 * Real.sqrt (badIntervalLongSaddleNumerator x H) := by
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := le_trans (by norm_num) hlog
  have hiterNonneg : 0 ≤ iteratedLog x := by
    rw [iteratedLog]
    exact Real.log_nonneg hlog
  have hA := badIntervalLongSaddleNumerator_ge hlog hlong
  have hANonneg : 0 ≤ badIntervalLongSaddleNumerator x H :=
    (mul_nonneg (mul_nonneg (by norm_num) hlogNonneg) hiterNonneg).trans hA
  have hsqrtLogNonneg : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hsqrtIterNonneg : 0 ≤ Real.sqrt (iteratedLog x) := Real.sqrt_nonneg _
  have hsqrtANonneg : 0 ≤ Real.sqrt (badIntervalLongSaddleNumerator x H) :=
    Real.sqrt_nonneg _
  have hsqrtLogSq : (Real.sqrt (Real.log (x : ℝ))) ^ 2 = Real.log (x : ℝ) :=
    Real.sq_sqrt hlogNonneg
  have hsqrtIterSq : (Real.sqrt (iteratedLog x)) ^ 2 = iteratedLog x :=
    Real.sq_sqrt hiterNonneg
  have hsqrtASq : (Real.sqrt (badIntervalLongSaddleNumerator x H)) ^ 2 =
      badIntervalLongSaddleNumerator x H := Real.sq_sqrt hANonneg
  have hsqrtTwoNonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtTwoSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let c := (3 * Real.sqrt (2 : ℝ) / 2) *
    Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (iteratedLog x)
  have hcNonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hcSq : c ^ 2 =
      (9 : ℝ) / 2 * Real.log (x : ℝ) * iteratedLog x := by
    calc
      c ^ 2 = (9 : ℝ) / 4 * (Real.sqrt (2 : ℝ)) ^ 2 *
          (Real.sqrt (Real.log (x : ℝ))) ^ 2 *
          (Real.sqrt (iteratedLog x)) ^ 2 := by
        dsimp only [c]
        ring
      _ = (9 : ℝ) / 2 * Real.log (x : ℝ) * iteratedLog x := by
        rw [hsqrtTwoSq, hsqrtLogSq, hsqrtIterSq]
        ring
  have hrootProduct :
      c ≤ Real.sqrt (badIntervalLongSaddleNumerator x H) := by
    apply (sq_le_sq₀ hcNonneg hsqrtANonneg).mp
    rw [hcSq, hsqrtASq]
    exact hA
  rw [taoZ, Real.log_exp]
  calc
    6 * ((1 / Real.sqrt 2) * Real.sqrt (Real.log (x : ℝ)) *
          Real.sqrt (iteratedLog x)) =
        2 * c := by
      dsimp only [c]
      field_simp [ne_of_gt hsqrtTwoPos]
      rw [hsqrtTwoSq]
      ring
    _ ≤ 2 * Real.sqrt (badIntervalLongSaddleNumerator x H) := by
      gcongr

/-- The corrected degree-two saddle still dominates four copies of Tao's
`z`-exponent. -/
theorem four_mul_log_taoZ_le_two_mul_sqrt_saddle_of_two
    {x H : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    4 * Real.log (taoZ x) ≤
      2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H) := by
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := le_trans (by norm_num) hlog
  have hiterNonneg : 0 ≤ iteratedLog x := by
    rw [iteratedLog]
    exact Real.log_nonneg hlog
  have hA := badIntervalLongSaddleNumeratorOfTwo_ge hlog hlong
  have hANonneg : 0 ≤ badIntervalLongSaddleNumeratorOfTwo x H :=
    (mul_nonneg (mul_nonneg (by norm_num) hlogNonneg) hiterNonneg).trans hA
  have hsqrtLogNonneg : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hsqrtIterNonneg : 0 ≤ Real.sqrt (iteratedLog x) := Real.sqrt_nonneg _
  have hsqrtANonneg : 0 ≤ Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H) :=
    Real.sqrt_nonneg _
  have hsqrtLogSq : (Real.sqrt (Real.log (x : ℝ))) ^ 2 = Real.log (x : ℝ) :=
    Real.sq_sqrt hlogNonneg
  have hsqrtIterSq : (Real.sqrt (iteratedLog x)) ^ 2 = iteratedLog x :=
    Real.sq_sqrt hiterNonneg
  have hsqrtASq : (Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H)) ^ 2 =
      badIntervalLongSaddleNumeratorOfTwo x H := Real.sq_sqrt hANonneg
  have hsqrtTwoPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtTwoSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let c := Real.sqrt (2 : ℝ) * Real.sqrt (Real.log (x : ℝ)) *
    Real.sqrt (iteratedLog x)
  have hcNonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hcSq : c ^ 2 =
      2 * Real.log (x : ℝ) * iteratedLog x := by
    calc
      c ^ 2 = (Real.sqrt (2 : ℝ)) ^ 2 *
          (Real.sqrt (Real.log (x : ℝ))) ^ 2 *
          (Real.sqrt (iteratedLog x)) ^ 2 := by
        dsimp only [c]
        ring
      _ = 2 * Real.log (x : ℝ) * iteratedLog x := by
        rw [hsqrtTwoSq, hsqrtLogSq, hsqrtIterSq]
  have hroot : c ≤ Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H) := by
    apply (sq_le_sq₀ hcNonneg hsqrtANonneg).mp
    rw [hcSq, hsqrtASq]
    have hprod : 0 ≤ Real.log (x : ℝ) * iteratedLog x :=
      mul_nonneg hlogNonneg hiterNonneg
    nlinarith
  rw [taoZ, Real.log_exp]
  calc
    4 * ((1 / Real.sqrt 2) * Real.sqrt (Real.log (x : ℝ)) *
          Real.sqrt (iteratedLog x)) = 2 * c := by
      dsimp only [c]
      field_simp [ne_of_gt hsqrtTwoPos]
      rw [hsqrtTwoSq]
      ring
    _ ≤ 2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H) := by
      gcongr

/-- Exponentiating the saddle comparison gives the precise sixth-power
saving in Tao's smoothness scale. -/
theorem exp_neg_two_sqrt_saddle_le_taoZ_pow_neg_six
    {x H : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumerator x H)) ≤
      1 / (taoZ x) ^ (6 : ℕ) := by
  have hsix := six_mul_log_taoZ_le_two_mul_sqrt_saddle hlog hlong
  calc
    Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumerator x H)) ≤
        Real.exp (-(6 * Real.log (taoZ x))) := by
      apply Real.exp_le_exp.mpr
      calc
        -2 * Real.sqrt (badIntervalLongSaddleNumerator x H) =
            -(2 * Real.sqrt (badIntervalLongSaddleNumerator x H)) := by ring
        _ ≤ -(6 * Real.log (taoZ x)) := neg_le_neg hsix
    _ = 1 / Real.exp (6 * Real.log (taoZ x)) := by
      simpa only [one_div] using
        (Real.exp_neg (6 * Real.log (taoZ x)))
    _ = 1 / (taoZ x) ^ (6 : ℕ) := by
      congr 1
      calc
        Real.exp (6 * Real.log (taoZ x)) =
            Real.exp (Real.log (taoZ x)) ^ (6 : ℕ) := by
          simpa using (Real.exp_nat_mul (Real.log (taoZ x)) 6)
        _ = (taoZ x) ^ (6 : ℕ) := by rw [Real.exp_log (taoZ_pos x)]

theorem exp_neg_two_sqrt_saddle_of_two_le_taoZ_pow_neg_four
    {x H : ℕ} (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H)) ≤
      1 / (taoZ x) ^ (4 : ℕ) := by
  have hfour := four_mul_log_taoZ_le_two_mul_sqrt_saddle_of_two hlog hlong
  calc
    Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H)) ≤
        Real.exp (-(4 * Real.log (taoZ x))) := by
      apply Real.exp_le_exp.mpr
      calc
        -2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H) =
            -(2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H)) := by ring
        _ ≤ -(4 * Real.log (taoZ x)) := neg_le_neg hfour
    _ = 1 / Real.exp (4 * Real.log (taoZ x)) := by
      simpa only [one_div] using
        (Real.exp_neg (4 * Real.log (taoZ x)))
    _ = 1 / (taoZ x) ^ (4 : ℕ) := by
      congr 1
      calc
        Real.exp (4 * Real.log (taoZ x)) =
            Real.exp (Real.log (taoZ x)) ^ (4 : ℕ) := by
          simpa using (Real.exp_nat_mul (Real.log (taoZ x)) 4)
        _ = (taoZ x) ^ (4 : ℕ) := by rw [Real.exp_log (taoZ_pos x)]

/-- The elementary AM--GM inequality in the exact reciprocal form used by
the `p₀`-saddle. -/
theorem two_mul_sqrt_le_div_add
    {A u : ℝ} (hA : 0 ≤ A) (hu : 0 < u) :
    2 * Real.sqrt A ≤ A / u + u := by
  have hsqrtNonneg : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
  have hsqrtSq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hsq := sq_nonneg (Real.sqrt A - u)
  have hmul : (2 * Real.sqrt A) * u ≤ (A / u + u) * u := by
    have huNe : u ≠ 0 := ne_of_gt hu
    field_simp [huNe]
    nlinarith
  exact le_of_mul_le_mul_right hmul hu

theorem exp_neg_div_sub_log_le_exp_neg_two_sqrt
    {A u : ℝ} (hA : 0 ≤ A) (hu : 0 < u) :
    Real.exp (-A / u - u) ≤ Real.exp (-2 * Real.sqrt A) := by
  apply Real.exp_le_exp.mpr
  calc
    -A / u - u = -(A / u + u) := by ring
    _ ≤ -(2 * Real.sqrt A) := neg_le_neg (two_mul_sqrt_le_div_add hA hu)
    _ = -2 * Real.sqrt A := by ring

/-- Writing one factor of `p₀⁻¹` exponentially exposes the exact AM--GM
saddle between `A/log(2p₀)` and `log(2p₀)`. -/
theorem inv_sq_mul_exp_neg_div_log_le
    {p₀ : ℕ} (hp₀ : 1 ≤ p₀) {A : ℝ} (hA : 0 ≤ A) :
    (1 / (p₀ : ℝ) ^ 2) *
        Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ))) ≤
      (2 / (p₀ : ℝ)) * Real.exp (-2 * Real.sqrt A) := by
  have hpPos : (0 : ℝ) < (p₀ : ℝ) := by exact_mod_cast hp₀
  have htwoPPos : (0 : ℝ) < ((2 * p₀ : ℕ) : ℝ) := by positivity
  have hu : 0 < Real.log (((2 * p₀ : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * p₀))
  have hsaddle := exp_neg_div_sub_log_le_exp_neg_two_sqrt hA hu
  calc
    (1 / (p₀ : ℝ) ^ 2) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ))) =
        (2 / (p₀ : ℝ)) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ)) -
            Real.log (((2 * p₀ : ℕ) : ℝ))) := by
      rw [Real.exp_sub, Real.exp_log htwoPPos]
      push_cast
      field_simp [ne_of_gt hpPos]
    _ ≤ (2 / (p₀ : ℝ)) * Real.exp (-2 * Real.sqrt A) := by
      gcongr

/-- The natural floor budget costs at most a factor four relative to
`x/p₀²` once the square scale is nonvacuous. -/
theorem cast_badIntervalCofactorBudget_add_one_le
    {x p₀ : ℕ} (hp₀ : 1 ≤ p₀) (hpSq : p₀ ^ 2 ≤ 2 * x) :
    ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      4 * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
  have hpPos : (0 : ℝ) < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hpSqPos : (0 : ℝ) < (p₀ : ℝ) ^ 2 := by positivity
  have hquot : ((badIntervalCofactorBudget x p₀ : ℕ) : ℝ) ≤
      (2 * (x : ℝ)) / (p₀ : ℝ) ^ 2 := by
    have hraw : (((2 * x / p₀ ^ 2 : ℕ)) : ℝ) ≤
        (((2 * x : ℕ) : ℝ)) / (((p₀ ^ 2 : ℕ) : ℝ)) := Nat.cast_div_le
    simpa only [badIntervalCofactorBudget, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_pow] using hraw
  have hone : (1 : ℝ) ≤ (2 * (x : ℝ)) / (p₀ : ℝ) ^ 2 := by
    exact (le_div_iff₀ hpSqPos).2 (by
      norm_num
      exact_mod_cast hpSq)
  norm_num [Nat.cast_add, Nat.cast_one]
  calc
    (badIntervalCofactorBudget x p₀ : ℝ) + 1 ≤
        (2 * (x : ℝ)) / (p₀ : ℝ) ^ 2 +
          (2 * (x : ℝ)) / (p₀ : ℝ) ^ 2 := by gcongr
    _ = 4 * (x : ℝ) / (p₀ : ℝ) ^ 2 := by ring

theorem four_mul_log_badIntervalCofactorBudget_le
    (x p₀ : ℕ) :
    4 * Real.log ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      4 * Real.log ((2 * x + 1 : ℕ) : ℝ) := by
  have hbudget : badIntervalCofactorBudget x p₀ + 1 ≤ 2 * x + 1 := by
    have hdiv : 2 * x / p₀ ^ 2 ≤ 2 * x := Nat.div_le_self _ _
    simpa only [badIntervalCofactorBudget] using Nat.add_le_add_right hdiv 1
  have hlog : Real.log ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      Real.log ((2 * x + 1 : ℕ) : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity)
      (by exact_mod_cast hbudget)
  gcongr

/-- Once `x` is large, the literal long range `cutoff ≤ H < p₀`
automatically supplies the large-prime hypothesis needed by the cofactor
sieve. -/
theorem eventually_badIntervalCofactor_large_of_long :
    ∀ᶠ x : ℕ in atTop, ∀ {p₀ H : ℕ},
      taoTypicalLengthCutoff x ≤ H → H < p₀ →
      4 * Real.log ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
        ((2 * p₀ : ℕ) : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_four_log_two_mul_add_one_le_lengthCutoff_rpow,
      hlog.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hscale hlogOne
  intro p₀ H hlong hHp₀
  have hcutOne : (1 : ℝ) ≤ taoTypicalLengthCutoff x := by
    calc
      (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := by
        exact one_le_pow₀ hlogOne
      _ ≤ taoTypicalLengthCutoff x := taoTypicalLengthCutoff_spec x
  have hcutRpow : (taoTypicalLengthCutoff x : ℝ) ^ ((3 : ℝ) / 50) ≤
      (taoTypicalLengthCutoff x : ℝ) := by
    calc
      (taoTypicalLengthCutoff x : ℝ) ^ ((3 : ℝ) / 50) ≤
          (taoTypicalLengthCutoff x : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hcutOne (by norm_num)
      _ = (taoTypicalLengthCutoff x : ℝ) := by rw [Real.rpow_one]
  have hcutToP : (taoTypicalLengthCutoff x : ℝ) ≤ (p₀ : ℝ) := by
    exact_mod_cast (hlong.trans (Nat.le_of_lt hHp₀))
  calc
    4 * Real.log ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
        4 * Real.log ((2 * x + 1 : ℕ) : ℝ) :=
      four_mul_log_badIntervalCofactorBudget_le x p₀
    _ ≤ (taoTypicalLengthCutoff x : ℝ) ^ ((3 : ℝ) / 50) := hscale
    _ ≤ (taoTypicalLengthCutoff x : ℝ) := hcutRpow
    _ ≤ (p₀ : ℝ) := hcutToP
    _ ≤ ((2 * p₀ : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      nlinarith [show (0 : ℝ) ≤ (p₀ : ℝ) by positivity]

/-- The same long range eventually pushes `p₀` past the fixed threshold in
the pinned prime-number-theorem count. -/
theorem eventually_card_badIntervalUpperPrimes_lower_of_long :
    ∀ᶠ x : ℕ in atTop, ∀ {p₀ H : ℕ},
      taoTypicalLengthCutoff x ≤ H → H < p₀ →
      ((2 * p₀ : ℕ) : ℝ) /
          (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
        ((badIntervalUpperPrimes p₀).card : ℝ) := by
  obtain ⟨a₀, ha₀⟩ :=
    eventually_atTop.1 eventually_card_badIntervalUpperPrimes_lower
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [hlog.eventually (eventually_ge_atTop (max 1 (a₀ : ℝ)))]
      with x hx
  intro p₀ H hlong hHp₀
  have hlogOne : (1 : ℝ) ≤ Real.log (x : ℝ) := (le_max_left _ _).trans hx
  have haLog : (a₀ : ℝ) ≤ Real.log (x : ℝ) := (le_max_right _ _).trans hx
  have hlogPow : Real.log (x : ℝ) ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ hlogOne (by norm_num : 1 ≤ (20 : ℕ)))
  have haCutReal : (a₀ : ℝ) ≤ taoTypicalLengthCutoff x :=
    haLog.trans (hlogPow.trans (taoTypicalLengthCutoff_spec x))
  have haP : a₀ ≤ p₀ := by
    have haCut : a₀ ≤ taoTypicalLengthCutoff x := by exact_mod_cast haCutReal
    exact haCut.trans (hlong.trans (Nat.le_of_lt hHp₀))
  exact ha₀ p₀ haP

theorem p₀_sq_le_two_mul_x_of_mem_scaleNormalizedBadIntervalStartsAt
    {x p₀ H N : ℕ} (hN : N ∈ scaleNormalizedBadIntervalStartsAt x p₀ H) :
    p₀ ^ 2 ≤ 2 * x := by
  obtain ⟨_hN, k, m, hnorm, _hxLower, hxUpper⟩ :=
    mem_scaleNormalizedBadIntervalStartsAt.mp hN
  obtain ⟨_hH, _hbad, hp₀, _hHp₀, _hpMax, hkMem, _hmSmooth,
    hkEq, _hkEndpoint, _hpow⟩ := hnorm
  have hkPos : 0 < k := by
    have := (Finset.mem_Ioc.mp hkMem).1
    omega
  have hmPos : 0 < m := by
    by_contra hm
    have hmZero : m = 0 := by omega
    subst m
    simp at hkEq
    omega
  have hpSqLeK : p₀ ^ 2 ≤ k := by
    rw [hkEq]
    exact Nat.le_mul_of_pos_right _ hmPos
  have hkLe : k ≤ 2 * x := (Finset.mem_Ioc.mp hkMem).2.trans hxUpper
  exact hpSqLeK.trans hkLe

theorem p₀_sq_le_two_mul_x_of_scaleNormalizedBadIntervalUnionAt_nonempty
    {x p₀ H : ℕ}
    (hne : (scaleNormalizedBadIntervalUnionAt x p₀ H).Nonempty) :
    p₀ ^ 2 ≤ 2 * x := by
  obtain ⟨n, hn⟩ := hne
  rw [scaleNormalizedBadIntervalUnionAt, Finset.mem_biUnion] at hn
  obtain ⟨N, hN, _hn⟩ := hn
  exact p₀_sq_le_two_mul_x_of_mem_scaleNormalizedBadIntervalStartsAt hN

/-- The canonical `k≥4` fixed fiber after the exact AM--GM saddle in `p₀`.
The remaining exponential no longer depends on `p₀`. -/
theorem scaleNormalizedBadIntervalUnionAt_le_saddle
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hH : 1 ≤ H) (hHp₀ : H < p₀) (hpSq : p₀ ^ 2 ≤ 2 * x)
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
      (128 * (x : ℝ) / (p₀ : ℝ)) *
        Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumerator x H)) := by
  let A := badIntervalLongSaddleNumerator x H
  have hxLog : 0 ≤ Real.log (((2 * x : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * x))
  have hHLog : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hA : 0 ≤ A := by
    dsimp only [A, badIntervalLongSaddleNumerator]
    positivity
  have hbudget := cast_badIntervalCofactorBudget_add_one_le hp₀ hpSq
  have hbudget' : (badIntervalCofactorBudget x p₀ : ℝ) + 1 ≤
      4 * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbudget
  have hfiber := scaleNormalizedBadIntervalUnionAt_le_canonicalDegreeExp
    hx hp₀ hH hHp₀ hcard hlarge hdegree hsmall
  have hsaddle := inv_sq_mul_exp_neg_div_log_le hp₀ hA
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        16 * (badIntervalCofactorBudget x p₀ + 1) *
          Real.exp (-(9 : ℝ) / 40 *
            (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
              Real.log (((2 * p₀ : ℕ) : ℝ)))) := hfiber
    _ = 16 * (badIntervalCofactorBudget x p₀ + 1) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ))) := by
      congr 2
      dsimp only [A, badIntervalLongSaddleNumerator]
      ring
    _ ≤ 16 * (4 * (x : ℝ) / (p₀ : ℝ) ^ 2) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ))) := by
      gcongr
    _ = 64 * (x : ℝ) *
        ((1 / (p₀ : ℝ) ^ 2) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ)))) := by ring
    _ ≤ 64 * (x : ℝ) *
        ((2 / (p₀ : ℝ)) * Real.exp (-2 * Real.sqrt A)) := by
      gcongr
    _ = (128 * (x : ℝ) / (p₀ : ℝ)) *
        Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumerator x H)) := by
      dsimp only [A]
      ring

/-- The corrected saddle estimate valid already at canonical degree two. -/
theorem scaleNormalizedBadIntervalUnionAt_le_saddle_of_two
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hH : 1 ≤ H) (hHp₀ : H < p₀) (hpSq : p₀ ^ 2 ≤ 2 * x)
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
      (128 * (x : ℝ) / (p₀ : ℝ)) *
        Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H)) := by
  let A := badIntervalLongSaddleNumeratorOfTwo x H
  have hxLog : 0 ≤ Real.log (((2 * x : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * x))
  have hHLog : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hA : 0 ≤ A := by
    dsimp only [A, badIntervalLongSaddleNumeratorOfTwo]
    positivity
  have hbudget := cast_badIntervalCofactorBudget_add_one_le hp₀ hpSq
  have hbudget' : (badIntervalCofactorBudget x p₀ : ℝ) + 1 ≤
      4 * (x : ℝ) / (p₀ : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbudget
  have hfiber := scaleNormalizedBadIntervalUnionAt_le_canonicalDegreeExp_of_two
    hx hp₀ hH hHp₀ hcard hlarge hdegree hsmall
  have hsaddle := inv_sq_mul_exp_neg_div_log_le hp₀ hA
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        16 * (badIntervalCofactorBudget x p₀ + 1) *
          Real.exp (-(11 : ℝ) / 100 *
            (Real.log (((2 * x : ℕ) : ℝ)) * Real.log (H : ℝ) /
              Real.log (((2 * p₀ : ℕ) : ℝ)))) := hfiber
    _ = 16 * (badIntervalCofactorBudget x p₀ + 1) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ))) := by
      congr 2
      dsimp only [A, badIntervalLongSaddleNumeratorOfTwo]
      ring
    _ ≤ 16 * (4 * (x : ℝ) / (p₀ : ℝ) ^ 2) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ))) := by
      gcongr
    _ = 64 * (x : ℝ) *
        ((1 / (p₀ : ℝ) ^ 2) *
          Real.exp (-A / Real.log (((2 * p₀ : ℕ) : ℝ)))) := by ring
    _ ≤ 64 * (x : ℝ) *
        ((2 / (p₀ : ℝ)) * Real.exp (-2 * Real.sqrt A)) := by
      gcongr
    _ = (128 * (x : ℝ) / (p₀ : ℝ)) *
        Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumeratorOfTwo x H)) := by
      dsimp only [A]
      ring

/-- The source-scale fixed-fiber conclusion in the canonical `k ≥ 4`
branch: the AM--GM saddle contributes a full factor `z(x)⁻⁶`. -/
theorem scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_six
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hH : 1 ≤ H) (hHp₀ : H < p₀) (hpSq : p₀ ^ 2 ≤ 2 * x)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ))
    (hdegree : 4 ≤ badIntervalCofactorSieveDegree x p₀)
    (hsmall : 8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50))
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (6 : ℕ)) := by
  have hsaddle := scaleNormalizedBadIntervalUnionAt_le_saddle
    hx hp₀ hH hHp₀ hpSq hcard hlarge hdegree hsmall
  have hdecay := exp_neg_two_sqrt_saddle_le_taoZ_pow_neg_six hlog hlong
  have hpPos : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hzPos := taoZ_pos x
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (128 * (x : ℝ) / (p₀ : ℝ)) *
          Real.exp (-2 * Real.sqrt (badIntervalLongSaddleNumerator x H)) :=
      hsaddle
    _ ≤ (128 * (x : ℝ) / (p₀ : ℝ)) *
          (1 / (taoZ x) ^ (6 : ℕ)) := by
      gcongr
    _ = 128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (6 : ℕ)) := by
      field_simp [ne_of_gt hpPos, ne_of_gt hzPos]

/-- Corrected source-scale fixed-fiber conclusion for every canonical degree
`k ≥ 2`. -/
theorem scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_four_of_two
    {x p₀ H : ℕ} (hx : 1 ≤ x) (hp₀ : 1 ≤ p₀)
    (hH : 1 ≤ H) (hHp₀ : H < p₀) (hpSq : p₀ ^ 2 ≤ 2 * x)
    (hcard : ((2 * p₀ : ℕ) : ℝ) /
        (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
      ((badIntervalUpperPrimes p₀).card : ℝ))
    (hlarge : 4 * Real.log
        ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
      ((2 * p₀ : ℕ) : ℝ))
    (hdegree : 2 ≤ badIntervalCofactorSieveDegree x p₀)
    (hsmall : 8 * (badIntervalCofactorSieveDegree x p₀ : ℝ) *
        Real.log ((2 * p₀ : ℕ) : ℝ) ≤
      (H : ℝ) ^ ((3 : ℝ) / 50))
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hlong : taoTypicalLengthCutoff x ≤ H) :
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
      128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
  have hsaddle := scaleNormalizedBadIntervalUnionAt_le_saddle_of_two
    hx hp₀ hH hHp₀ hpSq hcard hlarge hdegree hsmall
  have hdecay :=
    exp_neg_two_sqrt_saddle_of_two_le_taoZ_pow_neg_four hlog hlong
  have hpPos : 0 < (p₀ : ℝ) := by exact_mod_cast hp₀
  have hzPos := taoZ_pos x
  calc
    ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        (128 * (x : ℝ) / (p₀ : ℝ)) *
          Real.exp (-2 * Real.sqrt
            (badIntervalLongSaddleNumeratorOfTwo x H)) := hsaddle
    _ ≤ (128 * (x : ℝ) / (p₀ : ℝ)) *
          (1 / (taoZ x) ^ (4 : ℕ)) := by
      gcongr
    _ = 128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
      field_simp [ne_of_gt hpPos, ne_of_gt hzPos]

/-- Fully discharged long-fiber estimate on the source upper prime range
`p₀^20 ≤ x^3`.  Empty fibers are handled without imposing artificial scale
hypotheses; nonempty fibers supply `p₀² ≤ 2x` from their normalized witness. -/
theorem eventually_scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_four_of_long :
    ∀ᶠ x : ℕ in atTop, ∀ {p₀ H : ℕ},
      taoTypicalLengthCutoff x ≤ H → H < p₀ → p₀ ^ 20 ≤ x ^ 3 →
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (4 : ℕ)) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_ge_atTop (max 1 (8 ^ 10) : ℕ),
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_canonicalCofactorDenominator_le_of_long,
      eventually_card_badIntervalUpperPrimes_lower_of_long,
      eventually_badIntervalCofactor_large_of_long]
      with x hx hlogOne hdenominator hcardLong hlargeLong
  intro p₀ H hlong hHp₀ hscale
  by_cases hne : (scaleNormalizedBadIntervalUnionAt x p₀ H).Nonempty
  · have hxOne : 1 ≤ x := (le_max_left _ _).trans hx
    have hxHuge : 8 ^ 10 ≤ x := (le_max_right _ _).trans hx
    have hcutOne : 1 ≤ taoTypicalLengthCutoff x := by
      have hcutOneReal : (1 : ℝ) ≤ taoTypicalLengthCutoff x := by
        calc
          (1 : ℝ) ≤ (Real.log (x : ℝ)) ^ (20 : ℕ) := one_le_pow₀ hlogOne
          _ ≤ taoTypicalLengthCutoff x := taoTypicalLengthCutoff_spec x
      exact_mod_cast hcutOneReal
    have hH : 1 ≤ H := hcutOne.trans hlong
    have hp₀ : 1 ≤ p₀ := hH.trans (Nat.le_of_lt hHp₀)
    have hpSq : p₀ ^ 2 ≤ 2 * x :=
      p₀_sq_le_two_mul_x_of_scaleNormalizedBadIntervalUnionAt_nonempty hne
    have hdegree : 2 ≤ badIntervalCofactorSieveDegree x p₀ :=
      two_le_badIntervalCofactorSieveDegree_of_pow_twenty_le hxHuge hp₀ hscale
    exact scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_four_of_two
      hxOne hp₀ hH hHp₀ hpSq (hcardLong hlong hHp₀)
        (hlargeLong hlong hHp₀) hdegree (hdenominator hp₀ hlong)
        hlogOne hlong
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    norm_num only [Nat.cast_zero]
    have hpPos : (0 : ℝ) < (p₀ : ℝ) := by
      exact_mod_cast (by omega : 0 < p₀)
    apply div_nonneg
    · exact mul_nonneg (by norm_num) (Nat.cast_nonneg x)
    · exact mul_nonneg hpPos.le (pow_nonneg (taoZ_pos x).le 4)

/-- Eventual source-facing form of the `z(x)⁻⁶` fixed-fiber estimate.  The
literal long cutoff now discharges both the logarithmic lower bound on `x`
and the canonical-degree denominator comparison. -/
theorem eventually_scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_six :
    ∀ᶠ x : ℕ in atTop, ∀ {p₀ H : ℕ},
      1 ≤ p₀ → 1 ≤ H → H < p₀ → p₀ ^ 2 ≤ 2 * x →
      ((2 * p₀ : ℕ) : ℝ) /
          (4 * Real.log ((2 * p₀ : ℕ) : ℝ)) ≤
        ((badIntervalUpperPrimes p₀).card : ℝ) →
      4 * Real.log ((badIntervalCofactorBudget x p₀ + 1 : ℕ) : ℝ) ≤
        ((2 * p₀ : ℕ) : ℝ) →
      4 ≤ badIntervalCofactorSieveDegree x p₀ →
      taoTypicalLengthCutoff x ≤ H →
      ((scaleNormalizedBadIntervalUnionAt x p₀ H).card : ℝ) ≤
        128 * (x : ℝ) / ((p₀ : ℝ) * (taoZ x) ^ (6 : ℕ)) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_ge_atTop (1 : ℕ),
      hlog.eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_canonicalCofactorDenominator_le_of_long]
      with x hx hlogOne hdenominator
  intro p₀ H hp₀ hH hHp₀ hpSq hcard hlarge hdegree hlong
  exact scaleNormalizedBadIntervalUnionAt_le_taoZ_pow_neg_six
    hx hp₀ hH hHp₀ hpSq hcard hlarge hdegree
      (hdenominator hp₀ hlong) hlogOne hlong

end

end Tao2026
