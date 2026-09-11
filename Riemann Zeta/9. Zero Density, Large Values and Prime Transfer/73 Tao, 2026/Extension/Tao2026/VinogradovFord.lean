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
  have hrec := GafniTao.fordMomentCoefficient36_le_universal_four_power hR
    (n := vinogradovFordMultiplier R - 1) (by
      rw [show vinogradovFordMultiplier R - 1 + 1 =
        vinogradovFordMultiplier R by
          dsimp [vinogradovFordMultiplier]
          omega]
      exact hqFour)
  have hbase : (1 : ℝ) ≤ GafniTao.fordUniversalCoefficientBase R := by
    exact_mod_cast (show 1 ≤ GafniTao.fordUniversalCoefficientBase R by
      have := GafniTao.fordUniversalCoefficientBase_ge_two hR
      omega)
  have hq : vinogradovFordMultiplier R - 1 ≤ 4 * R :=
    (Nat.sub_le _ _).trans hqFour
  have hE : GafniTao.fordMomentCoefficientExponent R
      (vinogradovFordMultiplier R - 1) ≤ 57 * R ^ 3 := by
    unfold GafniTao.fordMomentCoefficientExponent
    have hRone : 1 ≤ R := by omega
    nlinarith [Nat.zero_le (R ^ 2), Nat.zero_le (R ^ 3),
      Nat.mul_le_mul_right (3 * R + R ^ 2) hq,
      Nat.mul_le_mul_left (2 * R)
        (Nat.mul_le_mul hq (show vinogradovFordMultiplier R - 1 + 1 ≤ 4 * R by
          rw [show vinogradovFordMultiplier R - 1 + 1 =
            vinogradovFordMultiplier R by
              dsimp [vinogradovFordMultiplier]
              omega]
          exact hqFour))]
  exact hrec.trans (pow_le_pow_right₀ hbase hE)

end

end Tao2026
