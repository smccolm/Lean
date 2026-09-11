import Tao2026.VinogradovMeanValue
import GafniTao.FordUniversalCoreCoefficient
import GafniTao.FordExpCertificate

/-!
# Supercritical Ford moments for Tao's polynomial bilinear estimate

This file packages the degree-uniform Ford moment used after equation (18).
The multiplier `3R + floor(R/5)` is far enough beyond the critical moment to
make Ford's permissible-exponent loss smaller than the sharpened coordinate
saving, while remaining inside the explicit Lemma 3.6 source range.
-/

namespace GafniTao

noncomputable section

/-- The universal endpoint estimate with the recurrence range enlarged from
`3k²` to `4k²`.  The same universal base has ample numerical room. -/
theorem fordLemma34Endpoint_le_universalBase_pow_four
    {s k : ℕ} (hk : 1000 ≤ k) (hs : s ≤ 4 * k ^ 2) :
    fordLemma34Endpoint s k ≤ fordUniversalCoefficientBase k ^ (k + 2) := by
  have hBtwo := fordUniversalCoefficientBase_ge_two hk
  have hBone : 1 ≤ fordUniversalCoefficientBase k := by omega
  have huniform := fordLemma34UniformBase_le_universalBase hk
  have hpoly : 50000 * k ^ 6 ≤ fordUniversalCoefficientBase k := by
    unfold fordUniversalCoefficientBase
    exact le_max_right _ _
  have hfirstNat : 4 * k ^ 4 + 2 ≤ fordUniversalCoefficientBase k := by
    have hk1 : 1 ≤ k := by omega
    have hk4to6 : k ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
    have hk6 : 1 ≤ k ^ 6 := one_le_pow₀ hk1
    exact (show 4 * k ^ 4 + 2 ≤ 50000 * k ^ 6 by omega).trans hpoly
  have hsourceNat : 64 * s ^ 2 + 1 ≤ fordUniversalCoefficientBase k := by
    have hsSq : s ^ 2 ≤ (4 * k ^ 2) ^ 2 := Nat.pow_le_pow_left hs 2
    have hsSq' : s ^ 2 ≤ 16 * k ^ 4 := by
      calc
        s ^ 2 ≤ (4 * k ^ 2) ^ 2 := hsSq
        _ = 16 * k ^ 4 := by ring
    have hk1 : 1 ≤ k := by omega
    have hk4to6 : k ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
    have hk6 : 1 ≤ k ^ 6 := one_le_pow₀ hk1
    exact (show 64 * s ^ 2 + 1 ≤ 50000 * k ^ 6 by omega).trans hpoly
  apply Nat.ceil_le.mpr
  unfold fordLemma34ExplicitThreshold
  apply max_le
  · have hcast : (((4 * k ^ 4 + 2 : ℕ) : ℝ)) ≤
        (fordUniversalCoefficientBase k : ℝ) := by exact_mod_cast hfirstNat
    exact hcast.trans (by
      exact_mod_cast (show fordUniversalCoefficientBase k ≤
          fordUniversalCoefficientBase k ^ (k + 2) by
        calc
          fordUniversalCoefficientBase k = fordUniversalCoefficientBase k ^ 1 := by simp
          _ ≤ fordUniversalCoefficientBase k ^ (k + 2) :=
            pow_le_pow_right₀ hBone (by omega)))
  · apply max_le
    · have hpow := pow_le_pow_left₀
        (zero_le_one.trans (fordLemma34UniformBase_one_le k)) huniform (k + 1)
      exact hpow.trans (by
        exact_mod_cast (pow_le_pow_right₀ hBone (by omega : k + 1 ≤ k + 2)))
    · have hsourceReal : (((64 * s ^ 2 + 1 : ℕ) : ℝ)) ≤
          (fordUniversalCoefficientBase k : ℝ) := by exact_mod_cast hsourceNat
      have hpow := pow_le_pow_left₀ (by positivity) hsourceReal 10
      exact hpow.trans (by
        exact_mod_cast (pow_le_pow_right₀ hBone (by omega : 10 ≤ k + 2)))

/-- Exact one-step coefficient estimate throughout the enlarged `4k²`
range. -/
theorem fordStepGlobalCoefficient_le_universal_power_exact_four
    {s k : ℕ} {C : ℝ} {E E' : ℕ}
    (hk : 1000 ≤ k) (hs : s ≤ 4 * k ^ 2)
    (hC0 : 0 ≤ C) (hC : C ≤ (fordUniversalCoefficientBase k : ℝ) ^ E)
    (hstepExp : E + (3 * k + (4 * s + k ^ 2)) ≤ E')
    (hfiniteExp : (k + 2) * (2 * (s + k)) ≤ E') :
    fordStepGlobalCoefficient s k C ≤
      (fordUniversalCoefficientBase k : ℝ) ^ E' := by
  let B : ℝ := fordUniversalCoefficientBase k
  have hBoneNat : 1 ≤ fordUniversalCoefficientBase k := by
    have := fordUniversalCoefficientBase_ge_two hk
    omega
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by
    simpa [B] using (by exact_mod_cast hBoneNat :
      (1 : ℝ) ≤ fordUniversalCoefficientBase k)
  have hkB : (k : ℝ) ≤ B := by
    simpa [B] using (by exact_mod_cast fordUniversalCoefficientBase_ge_k hk :
      (k : ℝ) ≤ fordUniversalCoefficientBase k)
  have hetaB : (53 / 50 : ℝ) ≤ B := by
    have htwo : (2 : ℝ) ≤ B := by
      simpa [B] using (by exact_mod_cast fordUniversalCoefficientBase_ge_two hk :
        (2 : ℝ) ≤ fordUniversalCoefficientBase k)
    linarith
  have hstepFactor :
      (k : ℝ) ^ (3 * k) *
          (53 / 50 : ℝ) ^ (4 * (s : ℝ) + (k : ℝ) ^ 2) ≤
        B ^ (3 * k + (4 * s + k ^ 2)) := by
    have hexpCast : 4 * (s : ℝ) + (k : ℝ) ^ 2 =
        ((4 * s + k ^ 2 : ℕ) : ℝ) := by norm_num
    rw [hexpCast, Real.rpow_natCast]
    calc
      (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * s + k ^ 2) ≤
          B ^ (3 * k) * B ^ (4 * s + k ^ 2) := by gcongr
      _ = B ^ (3 * k + (4 * s + k ^ 2)) :=
        (pow_add B (3 * k) (4 * s + k ^ 2)).symm
  have hstep : fordStepCoefficient35 s k C (53 / 50 : ℝ) ≤ B ^ E' := by
    unfold fordStepCoefficient35
    calc
      ((k : ℝ) ^ (3 * k) *
          (53 / 50 : ℝ) ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C ≤
          B ^ (3 * k + (4 * s + k ^ 2)) * B ^ E := by
        exact mul_le_mul hstepFactor hC hC0 (pow_nonneg hB0 _)
      _ = B ^ (E + (3 * k + (4 * s + k ^ 2))) := by
        rw [add_comm E, ← pow_add]
      _ ≤ B ^ E' := pow_le_pow_right₀ hB1 hstepExp
  have hendpoint := fordLemma34Endpoint_le_universalBase_pow_four hk hs
  have hfinite : ((fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k))) ≤ B ^ E' := by
    have hendpointReal : (fordLemma34Endpoint s k : ℝ) ≤ B ^ (k + 2) := by
      simpa [B] using (by exact_mod_cast hendpoint :
        (fordLemma34Endpoint s k : ℝ) ≤
          (fordUniversalCoefficientBase k : ℝ) ^ (k + 2))
    calc
      (fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k)) ≤
          (B ^ (k + 2)) ^ (2 * (s + k)) :=
        pow_le_pow_left₀ (by positivity) hendpointReal _
      _ = B ^ ((k + 2) * (2 * (s + k))) :=
        (pow_mul B (k + 2) (2 * (s + k))).symm
      _ ≤ B ^ E' := pow_le_pow_right₀ hB1 hfiniteExp
  exact max_le hstep hfinite

/-- The exact Lemma 3.6 recurrence has source-scale `O(k³)` coefficient
growth through every index below `4k`. -/
theorem fordMomentCoefficient36_le_universal_four_power
    {k n : ℕ} (hk : 1000 ≤ k) (hn : n + 1 ≤ 4 * k) :
    fordMomentCoefficient36 k n ≤
      (fordUniversalCoefficientBase k : ℝ) ^ fordMomentCoefficientExponent k n := by
  induction n with
  | zero =>
      rw [fordMomentCoefficient36_zero]
      have hfac : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
      have hkB : (k : ℝ) ≤ fordUniversalCoefficientBase k := by
        exact_mod_cast fordUniversalCoefficientBase_ge_k hk
      have hB1 : (1 : ℝ) ≤ fordUniversalCoefficientBase k := by
        exact_mod_cast (show 1 ≤ fordUniversalCoefficientBase k by
          have := fordUniversalCoefficientBase_ge_two hk
          omega)
      calc
        (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast hfac
        _ = (k : ℝ) ^ k := by norm_num
        _ ≤ (fordUniversalCoefficientBase k : ℝ) ^ k :=
          pow_le_pow_left₀ (by positivity) hkB k
        _ ≤ (fordUniversalCoefficientBase k : ℝ) ^ fordMomentCoefficientExponent k 0 :=
          pow_le_pow_right₀ hB1 (by simp [fordMomentCoefficientExponent])
  | succ n ih =>
      have hnprev : n + 1 ≤ 4 * k := by omega
      have hprev := ih hnprev
      have hs : (n + 1) * k ≤ 4 * k ^ 2 := by
        calc
          (n + 1) * k ≤ (4 * k) * k := Nat.mul_le_mul_right k hnprev
          _ = 4 * k ^ 2 := by ring
      have hfinite :
          (k + 2) * (2 * (((n + 1) * k) + k)) ≤
            fordMomentCoefficientExponent k (n + 1) := by
        have hnnext : n + 2 ≤ 4 * k := hn
        have hleft :
            (k + 2) * (2 * (((n + 1) * k) + k)) ≤ 20 * k ^ 3 := by
          have hrewrite : ((n + 1) * k) + k = (n + 2) * k := by ring
          rw [hrewrite]
          calc
            (k + 2) * (2 * ((n + 2) * k)) ≤
                (k + 2) * (2 * ((4 * k) * k)) := by gcongr
            _ ≤ 20 * k ^ 3 := by
              nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]
        exact hleft.trans (by unfold fordMomentCoefficientExponent; omega)
      rw [fordMomentCoefficient36_succ]
      apply fordStepGlobalCoefficient_le_universal_power_exact_four hk hs
          (fordMomentCoefficient36_nonneg k n) hprev
      · rw [fordMomentCoefficientExponent_succ]
      · exact hfinite

/-- Uniform cubic exponent bound for every recurrence coefficient in the
enlarged range.  This is the coefficient estimate needed when the moment is
pushed all the way to `4k²`. -/
theorem fordMomentCoefficient36_le_universal_cubic
    {k n : ℕ} (hk : 1000 ≤ k) (hn : n + 1 ≤ 4 * k) :
    fordMomentCoefficient36 k n ≤
      (fordUniversalCoefficientBase k : ℝ) ^ (57 * k ^ 3) := by
  have hrec := fordMomentCoefficient36_le_universal_four_power hk hn
  have hbase : (1 : ℝ) ≤ fordUniversalCoefficientBase k := by
    exact_mod_cast (show 1 ≤ fordUniversalCoefficientBase k by
      have := fordUniversalCoefficientBase_ge_two hk
      omega)
  have hn' : n ≤ 4 * k := by omega
  have hnSucc : n + 1 ≤ 4 * k := hn
  have hE : fordMomentCoefficientExponent k n ≤ 57 * k ^ 3 := by
    unfold fordMomentCoefficientExponent
    have hkOne : 1 ≤ k := by omega
    nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3),
      Nat.mul_le_mul_right (3 * k + k ^ 2) hn',
      Nat.mul_le_mul_left (2 * k) (Nat.mul_le_mul hn' hnSucc)]
  exact hrec.trans (pow_le_pow_right₀ hbase hE)

end

end GafniTao

namespace Tao2026

noncomputable section

open scoped BigOperators NNReal

/-- Integer multiplier used for the uniform supercritical Ford moment. -/
def vinogradovFordMultiplier (R : ℕ) : ℕ := 3 * R + R / 5

theorem exp_neg_589_div_100_le_one_div_350 :
    Real.exp (-(589 / 100 : ℝ)) ≤ 1 / 350 := by
  have h := GafniTao.real_exp_neg_le_scaledTaylor
    (z := (589 / 100 : ℝ)) (m := 6) (n := 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [GafniTao.fordExpTaylorUpper] at h ⊢
  exact h.trans (by norm_num)

theorem vinogradovFordMultiplier_le_sourceRange
    {R : ℕ} (hR : 1000 ≤ R) :
    (((vinogradovFordMultiplier R : ℕ) : ℝ)) ≤
      (R : ℝ) / 2 * (1 / 2 + Real.log (3 * (R : ℝ) / 8)) + 1 := by
  have hlogR := GafniTao.ford_log_k_lower hR
  have hlog38 : (-1 : ℝ) < Real.log (3 / 8 : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3 / 8)]
    rw [Real.exp_neg]
    have he : (8 / 3 : ℝ) < Real.exp 1 :=
      (by norm_num : (8 / 3 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
    have hrecip : 1 / Real.exp 1 < (3 / 8 : ℝ) := by
      rw [one_div_lt (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 3 / 8)]
      norm_num
      exact he
    simpa only [one_div] using hrecip
  have hlogarg : (59 / 10 : ℝ) < Real.log (3 * (R : ℝ) / 8) := by
    rw [show 3 * (R : ℝ) / 8 = (R : ℝ) * (3 / 8) by ring]
    rw [Real.log_mul (by positivity : (R : ℝ) ≠ 0)
      (by norm_num : (3 / 8 : ℝ) ≠ 0)]
    linarith
  have hdiv : (((R / 5 : ℕ) : ℝ)) ≤ (R : ℝ) / 5 := Nat.cast_div_le
  dsimp [vinogradovFordMultiplier]
  push_cast
  have hRR : (1000 : ℝ) ≤ R := by exact_mod_cast hR
  nlinarith

theorem vinogradovFord_exponent_le
    {R : ℕ} (hR : 1000 ≤ R) :
    1 / 2 - 2 * (((vinogradovFordMultiplier R : ℕ) : ℝ)) / (R : ℝ) +
        169 / (100 * (R : ℝ)) ≤ -(589 / 100 : ℝ) := by
  have hRpos : (0 : ℝ) < R := by positivity
  have hdivNat : R < 5 * (R / 5 + 1) := by omega
  have hdiv : (R : ℝ) / 5 - 1 < ((R / 5 : ℕ) : ℝ) := by
    have hcast : (R : ℝ) < 5 * (((R / 5 : ℕ) : ℝ) + 1) := by
      exact_mod_cast hdivNat
    linarith
  have hRR : (1000 : ℝ) ≤ R := by exact_mod_cast hR
  dsimp [vinogradovFordMultiplier]
  push_cast
  field_simp
  field_simp at hdiv
  nlinarith

/-- Ford's exact recurrence supplies the chosen supercritical moment with
permissible-exponent loss at most `3R²/2800`. -/
theorem vinogradovFord_supercritical_moment
    {R : ℕ} (hR : 1000 ≤ R) :
    GafniTao.FordVinogradovMomentBound
      (vinogradovFordMultiplier R * R) R
      (GafniTao.fordMomentCoefficient36 R (vinogradovFordMultiplier R - 1))
      ((3 / 2800 : ℝ) * (R : ℝ) ^ 2) := by
  have hqpos : 1 ≤ vinogradovFordMultiplier R := by
    dsimp [vinogradovFordMultiplier]
    omega
  have hqUpper : vinogradovFordMultiplier R ≤ R ^ 2 := by
    have hdiv : R / 5 ≤ R := Nat.div_le_self _ _
    dsimp [vinogradovFordMultiplier]
    nlinarith [Nat.zero_le (R ^ 2)]
  have hmoment := GafniTao.fordLemma36_moment_bound_quantitative
    hR hqpos hqUpper
  have hindex : 2 * R - 1 ≤ vinogradovFordMultiplier R - 1 := by
    dsimp [vinogradovFordMultiplier]
    omega
  have hsource : ((((vinogradovFordMultiplier R - 1) + 1 : ℕ) : ℝ)) ≤
      (R : ℝ) / 2 * (1 / 2 + Real.log (3 * (R : ℝ) / 8)) + 1 := by
    rw [show vinogradovFordMultiplier R - 1 + 1 =
      vinogradovFordMultiplier R by omega]
    exact vinogradovFordMultiplier_le_sourceRange hR
  have hdelta := GafniTao.fordLemma36_delta_exponent hR hindex hsource
  have hexponent :
      1 / 2 - 2 * ((((vinogradovFordMultiplier R - 1) + 1 : ℕ) : ℝ)) /
          (R : ℝ) + 169 / (100 * (R : ℝ)) ≤ -(589 / 100 : ℝ) := by
    rw [show vinogradovFordMultiplier R - 1 + 1 =
      vinogradovFordMultiplier R by omega]
    exact vinogradovFord_exponent_le hR
  have hdeltaTarget :
      GafniTao.fordDeltaSequence36 R (vinogradovFordMultiplier R - 1) ≤
        (3 / 2800 : ℝ) * (R : ℝ) ^ 2 := by
    calc
      GafniTao.fordDeltaSequence36 R (vinogradovFordMultiplier R - 1) ≤
          (3 / 8 : ℝ) * (R : ℝ) ^ 2 * Real.exp
            (1 / 2 - 2 * ((((vinogradovFordMultiplier R - 1) + 1 : ℕ) : ℝ)) /
              (R : ℝ) + 169 / (100 * (R : ℝ))) := hdelta
      _ ≤ (3 / 8 : ℝ) * (R : ℝ) ^ 2 * Real.exp (-(589 / 100 : ℝ)) := by
        gcongr
      _ ≤ (3 / 8 : ℝ) * (R : ℝ) ^ 2 * (1 / 350) := by
        gcongr
        exact exp_neg_589_div_100_le_one_div_350
      _ = (3 / 2800 : ℝ) * (R : ℝ) ^ 2 := by ring
  exact hmoment.mono_delta hdeltaTarget

/-- The exact recurrence coefficient at the chosen multiplier is controlled
by the universal base to an explicit cubic exponent. -/
theorem vinogradovFord_coefficient_le_universal_power
    {R : ℕ} (hR : 1000 ≤ R) :
    GafniTao.fordMomentCoefficient36 R (vinogradovFordMultiplier R - 1) ≤
      (GafniTao.fordUniversalCoefficientBase R : ℝ) ^ (57 * R ^ 3) := by
  have hqFour : vinogradovFordMultiplier R ≤ 4 * R := by
    have hdiv := Nat.div_le_self R 5
    dsimp [vinogradovFordMultiplier]
    omega
  exact GafniTao.fordMomentCoefficient36_le_universal_cubic hR
    (n := vinogradovFordMultiplier R - 1) (by
      rw [show vinogradovFordMultiplier R - 1 + 1 =
        vinogradovFordMultiplier R by
          dsimp [vinogradovFordMultiplier]
          omega]
      exact hqFour)

/-- The maximal multiplier allowed by the enlarged explicit recurrence. -/
def vinogradovFordFullMultiplier (R : ℕ) : ℕ := 4 * R

theorem exp_nine_lt_ten_thousand : Real.exp (9 : ℝ) < 10000 := by
  have hbase := GafniTao.real_exp_le_fordExpTaylorUpper
    (n := 20) (x := (9 / 10 : ℝ)) (by norm_num)
      (by norm_num [abs_of_nonneg])
  have hpow := pow_le_pow_left₀ (Real.exp_pos (9 / 10 : ℝ)).le hbase 10
  calc
    Real.exp (9 : ℝ) = Real.exp ((10 : ℝ) * (9 / 10 : ℝ)) := by norm_num
    _ = Real.exp (9 / 10 : ℝ) ^ (10 : ℕ) :=
      Real.exp_nat_mul (9 / 10 : ℝ) 10
    _ ≤ GafniTao.fordExpTaylorUpper 20 (9 / 10 : ℝ) ^ 10 := hpow
    _ < 10000 := by norm_num [GafniTao.fordExpTaylorUpper]

theorem log_ten_thousand_gt_nine : (9 : ℝ) < Real.log 10000 := by
  have h := exp_nine_lt_ten_thousand
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 10000)] at h
  exact Real.exp_lt_exp.mp h

/-- From degree `10000` onward, Ford's source range contains the full
multiplier `4R`. -/
theorem vinogradovFordFullMultiplier_le_sourceRange
    {R : ℕ} (hR : 10000 ≤ R) :
    (((vinogradovFordFullMultiplier R : ℕ) : ℝ)) ≤
      (R : ℝ) / 2 * (1 / 2 + Real.log (3 * (R : ℝ) / 8)) + 1 := by
  have hRR : (10000 : ℝ) ≤ R := by exact_mod_cast hR
  have hlogR : (9 : ℝ) < Real.log (R : ℝ) :=
    log_ten_thousand_gt_nine.trans_le
      (Real.strictMonoOn_log.monotoneOn (by norm_num)
        (show (0 : ℝ) < R by nlinarith) hRR)
  have hlog38 : (-1 : ℝ) < Real.log (3 / 8 : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3 / 8)]
    rw [Real.exp_neg]
    have he : (8 / 3 : ℝ) < Real.exp 1 :=
      (by norm_num : (8 / 3 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
    have hrecip : 1 / Real.exp 1 < (3 / 8 : ℝ) := by
      rw [one_div_lt (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 3 / 8)]
      norm_num
      exact he
    simpa only [one_div] using hrecip
  have hlogarg : (8 : ℝ) < Real.log (3 * (R : ℝ) / 8) := by
    rw [show 3 * (R : ℝ) / 8 = (R : ℝ) * (3 / 8) by ring]
    rw [Real.log_mul (by positivity : (R : ℝ) ≠ 0)
      (by norm_num : (3 / 8 : ℝ) ≠ 0)]
    linarith
  dsimp [vinogradovFordFullMultiplier]
  push_cast
  nlinarith

theorem exp_neg_thirty_seven_fifths_le_one_div_thousand :
    Real.exp (-(37 / 5 : ℝ)) ≤ 1 / 1000 := by
  have h := GafniTao.real_exp_neg_le_scaledTaylor
    (z := (37 / 5 : ℝ)) (m := 8) (n := 20)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [GafniTao.fordExpTaylorUpper] at h ⊢
  exact h.trans (by norm_num)

theorem vinogradovFordFull_exponent_le
    {R : ℕ} (hR : 1000 ≤ R) :
    1 / 2 - 2 * (((vinogradovFordFullMultiplier R : ℕ) : ℝ)) / (R : ℝ) +
        169 / (100 * (R : ℝ)) ≤ -(37 / 5 : ℝ) := by
  have hRpos : (0 : ℝ) < R := by positivity
  have hRR : (1000 : ℝ) ≤ R := by exact_mod_cast hR
  dsimp [vinogradovFordFullMultiplier]
  push_cast
  field_simp
  nlinarith

/-- The full explicit recurrence range yields a uniform supercritical moment
whose permissible loss is at most `3R²/8000`. -/
theorem vinogradovFord_full_moment
    {R : ℕ} (hR : 10000 ≤ R) :
    GafniTao.FordVinogradovMomentBound
      (vinogradovFordFullMultiplier R * R) R
      (GafniTao.fordMomentCoefficient36 R
        (vinogradovFordFullMultiplier R - 1))
      ((3 / 8000 : ℝ) * (R : ℝ) ^ 2) := by
  have hR1000 : 1000 ≤ R := by omega
  have hqpos : 1 ≤ vinogradovFordFullMultiplier R := by
    dsimp [vinogradovFordFullMultiplier]
    omega
  have hqUpper : vinogradovFordFullMultiplier R ≤ R ^ 2 := by
    dsimp [vinogradovFordFullMultiplier]
    nlinarith [Nat.zero_le (R ^ 2)]
  have hmoment := GafniTao.fordLemma36_moment_bound_quantitative
    hR1000 hqpos hqUpper
  have hindex : 2 * R - 1 ≤ vinogradovFordFullMultiplier R - 1 := by
    dsimp [vinogradovFordFullMultiplier]
    omega
  have hsource :
      ((((vinogradovFordFullMultiplier R - 1) + 1 : ℕ) : ℝ)) ≤
        (R : ℝ) / 2 * (1 / 2 + Real.log (3 * (R : ℝ) / 8)) + 1 := by
    rw [show vinogradovFordFullMultiplier R - 1 + 1 =
      vinogradovFordFullMultiplier R by
        dsimp [vinogradovFordFullMultiplier]
        omega]
    exact vinogradovFordFullMultiplier_le_sourceRange hR
  have hdelta := GafniTao.fordLemma36_delta_exponent hR1000 hindex hsource
  have hexponent :
      1 / 2 - 2 * ((((vinogradovFordFullMultiplier R - 1) + 1 : ℕ) : ℝ)) /
          (R : ℝ) + 169 / (100 * (R : ℝ)) ≤ -(37 / 5 : ℝ) := by
    rw [show vinogradovFordFullMultiplier R - 1 + 1 =
      vinogradovFordFullMultiplier R by
        dsimp [vinogradovFordFullMultiplier]
        omega]
    exact vinogradovFordFull_exponent_le hR1000
  have hdeltaTarget :
      GafniTao.fordDeltaSequence36 R (vinogradovFordFullMultiplier R - 1) ≤
        (3 / 8000 : ℝ) * (R : ℝ) ^ 2 := by
    calc
      GafniTao.fordDeltaSequence36 R (vinogradovFordFullMultiplier R - 1) ≤
          (3 / 8 : ℝ) * (R : ℝ) ^ 2 * Real.exp
            (1 / 2 - 2 *
              ((((vinogradovFordFullMultiplier R - 1) + 1 : ℕ) : ℝ)) /
              (R : ℝ) + 169 / (100 * (R : ℝ))) := hdelta
      _ ≤ (3 / 8 : ℝ) * (R : ℝ) ^ 2 * Real.exp (-(37 / 5 : ℝ)) := by
        gcongr
      _ ≤ (3 / 8 : ℝ) * (R : ℝ) ^ 2 * (1 / 1000) := by
        gcongr
        exact exp_neg_thirty_seven_fifths_le_one_div_thousand
      _ = (3 / 8000 : ℝ) * (R : ℝ) ^ 2 := by ring
  exact hmoment.mono_delta hdeltaTarget

theorem vinogradovFord_full_coefficient_le_universal_power
    {R : ℕ} (hR : 10000 ≤ R) :
    GafniTao.fordMomentCoefficient36 R
        (vinogradovFordFullMultiplier R - 1) ≤
      (GafniTao.fordUniversalCoefficientBase R : ℝ) ^ (57 * R ^ 3) := by
  apply GafniTao.fordMomentCoefficient36_le_universal_cubic (by omega)
  rw [show vinogradovFordFullMultiplier R - 1 + 1 =
    vinogradovFordFullMultiplier R by
      dsimp [vinogradovFordFullMultiplier]
      omega]
  simp [vinogradovFordFullMultiplier]

/-- The complete explicit coefficient in the full-range Ford bilinear bound
is uniformly bounded after its `32R⁴` extraction root. -/
theorem vinogradovFord_full_root_coefficient_le_absolute
    {R : ℕ} (hR : 10000 ≤ R) :
    let ell := vinogradovFordFullMultiplier R * R
    let m := ell * (2 * ell)
    let D :=
      (GafniTao.fordMomentCoefficient36 R
          (vinogradovFordFullMultiplier R - 1)) ^ 2 *
        (((3 * ell : ℕ) : ℝ) ^ (2 * R))
    D ^ (1 / (m : ℝ)) ≤ GafniTao.fordUniversalRootCoefficient := by
  dsimp only
  let ell := vinogradovFordFullMultiplier R * R
  let m := ell * (2 * ell)
  let C : ℝ := GafniTao.fordMomentCoefficient36 R
    (vinogradovFordFullMultiplier R - 1)
  let B : ℝ := GafniTao.fordUniversalCoefficientBase R
  let A : ℝ := GafniTao.fordAbsoluteCoefficientConstant
  let D : ℝ := C ^ 2 * (((3 * ell : ℕ) : ℝ) ^ (2 * R))
  have hR1000 : 1000 ≤ R := by omega
  have hRone : 1 ≤ R := by omega
  have hRreal : (0 : ℝ) < R := by positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ GafniTao.fordUniversalCoefficientBase R by
      have := GafniTao.fordUniversalCoefficientBase_ge_two hR1000
      omega)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast (show 1 ≤ GafniTao.fordAbsoluteCoefficientConstant by
      unfold GafniTao.fordAbsoluteCoefficientConstant
      exact (by norm_num : 1 ≤ 50000).trans (le_max_right _ _))
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact GafniTao.fordMomentCoefficient36_nonneg _ _
  have hC : C ≤ B ^ (57 * R ^ 3) := by
    dsimp only [C, B]
    exact vinogradovFord_full_coefficient_le_universal_power hR
  have hCsq : C ^ 2 ≤ B ^ (114 * R ^ 3) := by
    calc
      C ^ 2 ≤ (B ^ (57 * R ^ 3)) ^ 2 :=
        pow_le_pow_left₀ hC0 hC _
      _ = B ^ ((57 * R ^ 3) * 2) := (pow_mul B (57 * R ^ 3) 2).symm
      _ = B ^ (114 * R ^ 3) := by congr 1; ring
  have hcoordBaseNat : 3 * ell ≤ GafniTao.fordUniversalCoefficientBase R := by
    have hpoly : 50000 * R ^ 6 ≤ GafniTao.fordUniversalCoefficientBase R := by
      unfold GafniTao.fordUniversalCoefficientBase
      exact le_max_right _ _
    have hRpow : R ^ 2 ≤ R ^ 6 :=
      pow_le_pow_right₀ hRone (by norm_num)
    dsimp only [ell, vinogradovFordFullMultiplier]
    exact (calc
      3 * (4 * R * R) = 12 * R ^ 2 := by ring
      _ ≤ 50000 * R ^ 2 := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 50000 * R ^ 6 := Nat.mul_le_mul_left _ hRpow).trans hpoly
  have hcoordBase : (((3 * ell : ℕ) : ℝ)) ≤ B := by
    dsimp only [B]
    exact_mod_cast hcoordBaseNat
  have hcoord : (((3 * ell : ℕ) : ℝ) ^ (2 * R)) ≤ B ^ (2 * R) :=
    pow_le_pow_left₀ (by positivity) hcoordBase _
  have hexponent : 114 * R ^ 3 + 2 * R ≤ 115 * R ^ 3 := by
    nlinarith [one_le_pow₀ hRone (n := 2)]
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDbound : D ≤ B ^ (115 * R ^ 3) := by
    dsimp only [D]
    calc
      C ^ 2 * (((3 * ell : ℕ) : ℝ) ^ (2 * R)) ≤
          B ^ (114 * R ^ 3) * B ^ (2 * R) := by gcongr
      _ = B ^ (114 * R ^ 3 + 2 * R) := by rw [← pow_add]
      _ ≤ B ^ (115 * R ^ 3) := pow_le_pow_right₀ hB1 hexponent
  have hm : m = 32 * R ^ 4 := by
    dsimp only [m, ell, vinogradovFordFullMultiplier]
    ring
  let q : ℝ := 115 / (32 * (R : ℝ))
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq8 : q ≤ 8 := by
    dsimp [q]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * R)]
    nlinarith [show (1 : ℝ) ≤ R by exact_mod_cast hRone]
  have hbaseNat := GafniTao.fordUniversalCoefficientBase_le_absolute_mul hR1000
  have hbase : B ≤ A * (R : ℝ) ^ 6 := by
    dsimp only [B, A]
    exact_mod_cast hbaseNat
  have hRqNat := GafniTao.ford_k_pow_six_le_two_pow hRone
  have hRq : (R : ℝ) ^ 6 ≤ (2 : ℝ) ^ (12 * R) := by
    exact_mod_cast hRqNat
  have hAq : A ^ q ≤ A ^ (8 : ℕ) := by
    calc
      A ^ q ≤ A ^ (8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hA1 hq8
      _ = A ^ (8 : ℕ) := Real.rpow_natCast A 8
  have htwoq : (2 : ℝ) ^ (345 / 8 : ℝ) ≤ (2 : ℝ) ^ (96 : ℕ) := by
    calc
      (2 : ℝ) ^ (345 / 8 : ℝ) ≤ (2 : ℝ) ^ (96 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (345 / 8 : ℝ) ≤ 96)
      _ = (2 : ℝ) ^ (96 : ℕ) := Real.rpow_natCast 2 96
  have hrootBound := Real.rpow_le_rpow hD0 hDbound
    (by positivity : 0 ≤ (1 / (m : ℝ)))
  calc
    D ^ (1 / (m : ℝ)) ≤ (B ^ (115 * R ^ 3)) ^ (1 / (m : ℝ)) :=
      hrootBound
    _ = B ^ q := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
      dsimp only [q]
      rw [hm]
      push_cast
      field_simp
    _ ≤ (A * (R : ℝ) ^ 6) ^ q := Real.rpow_le_rpow hB0 hbase hq0
    _ = A ^ q * ((R : ℝ) ^ 6) ^ q := by
      rw [Real.mul_rpow hA0 (by positivity)]
    _ ≤ A ^ 8 * (((2 : ℝ) ^ (12 * R)) ^ q) := by
      gcongr
    _ = A ^ 8 * (2 : ℝ) ^ (345 / 8 : ℝ) := by
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      dsimp only [q]
      push_cast
      field_simp
      ring_nf
    _ ≤ A ^ 8 * (2 : ℝ) ^ 96 := by
      gcongr
    _ = GafniTao.fordUniversalRootCoefficient := rfl

/-- Exact equation-(18) exponent ledger at an arbitrary supercritical
moment.  The main term `2ell-κ_R` cancels against the coordinate-box degree
sum just as at the critical moment. -/
theorem supercritical_vinogradov_power_rpow_identity
    (R V ell : ℕ) (hV : 1 ≤ V) (hell : 1 ≤ ell)
    (C A Δ δ : ℝ) :
    (V : ℝ) ^ ((ell - 1) * (2 * ell)) *
        ((((V ^ ell : ℕ) : ℝ) ^ (2 * ell - 2) *
          (C * (V : ℝ) ^
            (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) *
            ((C * (V : ℝ) ^
              (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) *
              ((V : ℝ) ^ (-δ) *
                (A * (V : ℝ) ^ (R * (R + 1))))))) =
      C ^ 2 * A * (V : ℝ) ^ ((4 * ell ^ 2 : ℕ) + 2 * Δ - δ) := by
  have hVpos : (0 : ℝ) < V := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hV)
  have hk : (2 : ℝ) * GafniTao.fordVinogradovKappa R =
      (R : ℝ) * (R + 1) := by
    exact_mod_cast two_mul_fordVinogradovKappa R
  rw [show (((V ^ ell : ℕ) : ℝ)) = (V : ℝ) ^ ell by norm_cast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hVpos.le]
  have hmoment :
      ((V : ℝ) ^
        (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) ^ 2 =
        (V : ℝ) ^
          (2 * (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
    congr 1
    ring
  have hmoment' :
      ((V : ℝ) ^
        ((ell : ℝ) * 2 - GafniTao.fordVinogradovKappa R + Δ)) ^ 2 =
        (V : ℝ) ^
          (2 * (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) := by
    simpa [mul_comm] using hmoment
  ring_nf
  rw [hmoment']
  have hpowers :
      (V : ℝ) ^ (((ell - 1) * (2 * ell) : ℕ) : ℝ) *
          (V : ℝ) ^ ((ell : ℝ) * ((2 * ell - 2 : ℕ) : ℝ)) *
          (V : ℝ) ^
            (2 * (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) *
          (V : ℝ) ^ (-δ) *
          (V : ℝ) ^ ((R * (R + 1) : ℕ) : ℝ) =
        (V : ℝ) ^ (((4 * ell ^ 2 : ℕ) : ℝ) + 2 * Δ - δ) := by
    repeat' rw [← Real.rpow_add hVpos]
    congr 1
    have hellSub : ell - 1 + 1 = ell := by omega
    have htwoSub : 2 * ell - 2 + 2 = 2 * ell := by omega
    have hellSubR : ((ell - 1 : ℕ) : ℝ) + 1 = ell := by exact_mod_cast hellSub
    have htwoSubR : ((2 * ell - 2 : ℕ) : ℝ) + 2 = 2 * ell := by
      exact_mod_cast htwoSub
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      at hk ⊢
    nlinarith
  ring_nf at hpowers
  convert congrArg (fun z : ℝ => C ^ 2 * A * z) hpowers using 1
  all_goals ring_nf

/-- Equation (18) composed with a supercritical Ford-shaped mean-value
estimate.  Only the permissible loss `Δ`, not the distance above the
critical moment, survives in the scale exponent. -/
theorem powered_bilinear_supercritical_bound_of_meanValue_and_coordinate_bounds
    (c : ℕ → ℝ) (R V ell : ℕ) (hV : 1 ≤ V) (hell : 1 ≤ ell)
    {C Δ δ A : ℝ} (hC0 : 0 ≤ C)
    (hJ : (vinogradovMeanValueCount ell R V : ℝ) ≤
      C * (V : ℝ) ^
        (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ))
    (hP : (∏ j : Fin R,
      ∑ x ∈ vinogradovPowerBoxSide ell V (j.1 + 1),
        ‖∑ y ∈ vinogradovPowerBoxSide ell V (j.1 + 1),
          standardAdditiveCharacter
            (c (j.1 + 1) * (x : ℝ) * (y : ℝ))‖) ≤
      (V : ℝ) ^ (-δ) *
        (A * (V : ℝ) ^ (R * (R + 1)))) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ell * (2 * ell)) ≤
      C ^ 2 * A *
        (V : ℝ) ^ ((4 * ell ^ 2 : ℕ) + 2 * Δ - δ) := by
  calc
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ell * (2 * ell)) ≤
      (V : ℝ) ^ ((ell - 1) * (2 * ell)) *
        ((((V ^ ell : ℕ) : ℝ) ^ (2 * ell - 2) *
          (C * (V : ℝ) ^
            (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) *
            ((C * (V : ℝ) ^
              (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ)) *
              ((V : ℝ) ^ (-δ) *
                (A * (V : ℝ) ^ (R * (R + 1))))))) := by
      exact powered_bilinear_bound_of_meanValue_and_coordinate_bounds
        c R V ell hell hJ hP
          (mul_nonneg hC0 (Real.rpow_nonneg (by positivity) _))
    _ = C ^ 2 * A *
        (V : ℝ) ^ ((4 * ell ^ 2 : ℕ) + 2 * Δ - δ) :=
      supercritical_vinogradov_power_rpow_identity R V ell hV hell C A Δ δ

/-- Tao's sharp quarter-window coordinate saving combined with the full
explicit Ford moment.  This is the first coefficient-uniform powered bound
in the high-degree branch and no longer uses the qualitative Wooley
constant. -/
theorem source_powered_bilinear_ford_full_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hRlarge : 10000 ≤ vinogradovTaylorDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let R := vinogradovTaylorDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier R * R
    ‖vinogradovBilinearPolynomialSum c R V‖ ^ (ell * (2 * ell)) ≤
      (GafniTao.fordMomentCoefficient36 R
          (vinogradovFordFullMultiplier R - 1)) ^ 2 *
        (((3 * ell : ℕ) : ℝ) ^ (2 * R)) *
        (V : ℝ) ^
          ((4 * ell ^ 2 : ℕ) +
            2 * ((3 / 8000 : ℝ) * (R : ℝ) ^ 2) -
              255 * (R : ℝ) ^ 2 / 197632) := by
  dsimp only
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier R * R
  let C := GafniTao.fordMomentCoefficient36 R
    (vinogradovFordFullMultiplier R - 1)
  let Δ : ℝ := (3 / 8000) * (R : ℝ) ^ 2
  let δ : ℝ := 255 * (R : ℝ) ^ 2 / 197632
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hell : 1 ≤ ell := by
    dsimp only [ell, vinogradovFordFullMultiplier]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))
  have hmoment : GafniTao.FordVinogradovMomentBound ell R C Δ := by
    dsimp only [ell, R, C, Δ]
    exact vinogradovFord_full_moment hRlarge
  have hJraw := vinogradovMeanValueCount_le_of_fordVinogradovMomentBound
    hmoment V hV
  have hJ : (vinogradovMeanValueCount ell R V : ℝ) ≤
      C * (V : ℝ) ^
        (2 * (ell : ℝ) - GafniTao.fordVinogradovKappa R + Δ) := by
    simpa only [GafniTao.fordLambda34,
      GafniTao.fordVinogradovKappa_cast] using hJraw
  have hP := source_prod_coordinateSums_le_quarterSaving_mul_criticalPower
    (ell := ell) hX hFhigh hα hn hell hcoeff hsmall
  have hassembled :=
    powered_bilinear_supercritical_bound_of_meanValue_and_coordinate_bounds
      c R V ell hV hell (C := C) (Δ := Δ) (δ := δ)
        (A := (((3 * ell : ℕ) : ℝ) ^ (2 * R)))
        (zero_le_one.trans hmoment.one_le_coefficient) hJ
        (by
          simpa only [R, V, δ, neg_div] using hP)
  dsimp only [R, V, ell, C, Δ, δ] at hassembled ⊢
  exact hassembled

/-- Net scale saving left after paying for the two explicit Ford permissible
exponents. -/
def vinogradovFordFullSaving (R : ℕ) : ℝ :=
  (255 / 197632 - 3 / 4000 : ℝ) * (R : ℝ) ^ 2

theorem vinogradovFordFullSaving_pos {R : ℕ} (hR : 1 ≤ R) :
    0 < vinogradovFordFullSaving R := by
  unfold vinogradovFordFullSaving
  positivity

/-- At the source degree `R=10⌈s⌉`, the full-range Ford root saving is
strictly smaller than Tao's required `4·2⁻¹⁸/s²`.  Thus the uniform benchmark
is a genuine power saving but cannot close the pinned source proposition. -/
theorem vinogradovFordFull_root_saving_lt_sourceTarget
    {s : ℝ} {R : ℕ} (hs : 0 < s) (hR : R = 10 * ⌈s⌉₊) :
    vinogradovFordFullSaving R /
        (((vinogradovFordFullMultiplier R * R) *
          (2 * (vinogradovFordFullMultiplier R * R)) : ℕ) : ℝ) <
      4 * (2 : ℝ) ^ (-18 : ℝ) / s ^ 2 := by
  have hceil : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
  have hRcast : (R : ℝ) = 10 * (⌈s⌉₊ : ℝ) := by
    norm_num [hR]
  have hRs : 10 * s ≤ (R : ℝ) := by
    rw [hRcast]
    linarith
  have hRpos : (0 : ℝ) < R := by nlinarith
  have hm :
      (((vinogradovFordFullMultiplier R * R) *
        (2 * (vinogradovFordFullMultiplier R * R)) : ℕ) : ℝ) =
        32 * (R : ℝ) ^ 4 := by
    dsimp only [vinogradovFordFullMultiplier]
    push_cast
    ring
  have hsaving :
      vinogradovFordFullSaving R / (32 * (R : ℝ) ^ 4) =
        (255 / 197632 - 3 / 4000 : ℝ) / (32 * (R : ℝ) ^ 2) := by
    unfold vinogradovFordFullSaving
    field_simp
  have hden : 3200 * s ^ 2 ≤ 32 * (R : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((R : ℝ) - 10 * s)]
  have hinv :
      1 / (32 * (R : ℝ) ^ 2) ≤ 1 / (3200 * s ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hden
  have hc0 : 0 ≤ (255 / 197632 - 3 / 4000 : ℝ) := by norm_num
  have hscale :
      (255 / 197632 - 3 / 4000 : ℝ) / (32 * (R : ℝ) ^ 2) ≤
        (255 / 197632 - 3 / 4000 : ℝ) / (3200 * s ^ 2) := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left hinv hc0
  have hnumeric :
      (255 / 197632 - 3 / 4000 : ℝ) / 3200 < 1 / 65536 := by
    norm_num
  rw [hm, hsaving]
  calc
    (255 / 197632 - 3 / 4000 : ℝ) / (32 * (R : ℝ) ^ 2) ≤
        (255 / 197632 - 3 / 4000 : ℝ) / (3200 * s ^ 2) := hscale
    _ = ((255 / 197632 - 3 / 4000 : ℝ) / 3200) / s ^ 2 := by ring
    _ < (1 / 65536 : ℝ) / s ^ 2 :=
      div_lt_div_of_pos_right hnumeric (sq_pos_of_pos hs)
    _ = 4 * (2 : ℝ) ^ (-18 : ℝ) / s ^ 2 := by norm_num

/-- Exact root extraction from the full-range Ford moment.  This gives a
genuine positive power saving with a fully explicit coefficient.  It is an
auxiliary quantitative check, not the source endpoint: the supercritical
moment has a larger extraction root, so this saving does not reach Tao's
fixed `2^-18` decay. -/
theorem source_bilinear_ford_full_root_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hRlarge : 10000 ≤ vinogradovTaylorDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let R := vinogradovTaylorDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier R * R
    let m := ell * (2 * ell)
    let D :=
      (GafniTao.fordMomentCoefficient36 R
          (vinogradovFordFullMultiplier R - 1)) ^ 2 *
        (((3 * ell : ℕ) : ℝ) ^ (2 * R))
    ‖vinogradovBilinearPolynomialSum c R V‖ ≤
      D ^ (1 / (m : ℝ)) * (V : ℝ) ^ (2 : ℕ) *
        (V : ℝ) ^ (-vinogradovFordFullSaving R / (m : ℝ)) := by
  dsimp only
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier R * R
  let m := ell * (2 * ell)
  let D : ℝ :=
    (GafniTao.fordMomentCoefficient36 R
        (vinogradovFordFullMultiplier R - 1)) ^ 2 *
      (((3 * ell : ℕ) : ℝ) ^ (2 * R))
  have hpow := source_powered_bilinear_ford_full_bound_quarter
    hX hFhigh hα hn hRlarge hcoeff hsmall
  have hm : 1 ≤ m := by
    dsimp only [m, ell, vinogradovFordFullMultiplier]
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))
        (mul_ne_zero (by norm_num)
          (mul_ne_zero (mul_ne_zero (by norm_num) (by omega)) (by omega))))
  have hV : (0 : ℝ) < V := by
    exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hpow' :
      ‖vinogradovBilinearPolynomialSum c R V‖ ^ m ≤
        D * (V : ℝ) ^ (((2 * m : ℕ) : ℝ) - vinogradovFordFullSaving R) := by
    dsimp only [R, V, ell, m, D] at hpow ⊢
    convert hpow using 1
    congr 2
    unfold vinogradovFordFullSaving
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hroot := le_root_mul_sq_mul_saving_of_pow_le hm
    (norm_nonneg _) hD hV hpow'
  dsimp only [R, V, ell, m, D] at hroot ⊢
  exact hroot

/-- Uniform unconditional form of the full-range Ford benchmark.  It removes
all degree dependence from the coefficient while retaining the (weaker than
source-target) positive scale saving. -/
theorem source_bilinear_ford_full_uniform_bound_quarter
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hRlarge : 10000 ≤ vinogradovTaylorDegree X F)
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    let R := vinogradovTaylorDegree X F
    let V := vinogradovAveragingRange X
    let ell := vinogradovFordFullMultiplier R * R
    let m := ell * (2 * ell)
    ‖vinogradovBilinearPolynomialSum c R V‖ ≤
      GafniTao.fordUniversalRootCoefficient * (V : ℝ) ^ (2 : ℕ) *
        (V : ℝ) ^ (-vinogradovFordFullSaving R / (m : ℝ)) := by
  dsimp only
  let R := vinogradovTaylorDegree X F
  let V := vinogradovAveragingRange X
  let ell := vinogradovFordFullMultiplier R * R
  let m := ell * (2 * ell)
  let D : ℝ :=
    (GafniTao.fordMomentCoefficient36 R
        (vinogradovFordFullMultiplier R - 1)) ^ 2 *
      (((3 * ell : ℕ) : ℝ) ^ (2 * R))
  have hroot := source_bilinear_ford_full_root_bound_quarter
    hX hFhigh hα hn hRlarge hcoeff hsmall
  have hDroot : D ^ (1 / (m : ℝ)) ≤
      GafniTao.fordUniversalRootCoefficient := by
    dsimp only [D, m, ell, R]
    exact vinogradovFord_full_root_coefficient_le_absolute hRlarge
  dsimp only [R, V, ell, m, D] at hroot ⊢
  exact hroot.trans (by gcongr)

end

end Tao2026
