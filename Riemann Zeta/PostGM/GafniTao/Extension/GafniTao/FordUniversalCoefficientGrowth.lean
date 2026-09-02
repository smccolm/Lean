import GafniTao.FordCoefficientGrowth

/-!
# Uniform-in-degree coefficient bookkeeping

The PNT threshold is an absolute scale, not a lower bound on Ford's degree.
Putting it into the coefficient base makes the Lemma 3.5 recurrence available
for every `k ≥ 1000`.  The base remains a fixed constant times `k⁶`, so its
contribution is absolute after the `8k⁴`-th root.
-/

namespace GafniTao

noncomputable section

def fordUniversalCoefficientBase (k : ℕ) : ℕ :=
  max (fordUniformPrimeThreshold + 1) (50000 * k ^ 6)

def fordAbsoluteCoefficientConstant : ℕ :=
  max (fordUniformPrimeThreshold + 1) 50000

theorem fordUniversalCoefficientBase_ge_two
    {k : ℕ} (hk : 1000 ≤ k) : 2 ≤ fordUniversalCoefficientBase k := by
  unfold fordUniversalCoefficientBase
  exact le_max_of_le_right (by
    have hk1 : 1 ≤ k := by omega
    have hkpow : 1 ≤ k ^ 6 := one_le_pow₀ hk1
    omega)

theorem fordUniversalCoefficientBase_ge_k
    {k : ℕ} (hk : 1000 ≤ k) :
    k ≤ fordUniversalCoefficientBase k := by
  unfold fordUniversalCoefficientBase
  apply le_max_of_le_right
  have hk1 : 1 ≤ k := by omega
  calc
    k = k ^ 1 := by simp
    _ ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
    _ ≤ 50000 * k ^ 6 := Nat.le_mul_of_pos_left _ (by norm_num)

theorem fordPrimePacketScaleThreshold_le_universalBase
    {k : ℕ} (hk : 1000 ≤ k) :
    fordPrimePacketScaleThreshold k + 1 ≤ fordUniversalCoefficientBase k := by
  have hk1 : 1 ≤ k := by omega
  unfold fordPrimePacketScaleThreshold fordUniversalCoefficientBase
  by_cases h : fordUniformPrimeThreshold ≤ (200 * k ^ 3) ^ 2
  · rw [max_eq_right h]
    apply le_max_of_le_right
    calc
      (200 * k ^ 3) ^ 2 + 1 = 40000 * k ^ 6 + 1 := by ring
      _ ≤ 50000 * k ^ 6 := by
        have hkpow : 1 ≤ k ^ 6 := one_le_pow₀ hk1
        omega
  · have h' : (200 * k ^ 3) ^ 2 ≤ fordUniformPrimeThreshold :=
      le_of_not_ge h
    rw [max_eq_left h']
    exact le_max_left _ _

theorem fordLemma34UniformBase_le_universalBase
    {k : ℕ} (hk : 1000 ≤ k) :
    fordLemma34UniformBase k ≤ (fordUniversalCoefficientBase k : ℝ) := by
  unfold fordLemma34UniformBase
  apply max_le
  · exact_mod_cast fordUniversalCoefficientBase_ge_k hk
  · exact_mod_cast fordPrimePacketScaleThreshold_le_universalBase hk

theorem fordLemma34Endpoint_le_universalBase_pow
    {s k : ℕ} (hk : 1000 ≤ k) (hs : s ≤ 3 * k ^ 2) :
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
    have hsSq : s ^ 2 ≤ (3 * k ^ 2) ^ 2 := Nat.pow_le_pow_left hs 2
    have hsSq' : s ^ 2 ≤ 9 * k ^ 4 := by
      calc
        s ^ 2 ≤ (3 * k ^ 2) ^ 2 := hsSq
        _ = 9 * k ^ 4 := by ring
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

theorem fordStepGlobalCoefficient_le_universal_power_exact
    {s k : ℕ} {C : ℝ} {E E' : ℕ}
    (hk : 1000 ≤ k) (hs : s ≤ 3 * k ^ 2)
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
  have hendpoint := fordLemma34Endpoint_le_universalBase_pow hk hs
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

theorem fordMomentCoefficient36_le_universal_sharp_power
    {k n : ℕ} (hk : 1000 ≤ k) (hn : n + 1 ≤ 3 * k) :
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
      have hnprev : n + 1 ≤ 3 * k := by omega
      have hprev := ih hnprev
      have hs : (n + 1) * k ≤ 3 * k ^ 2 := by
        calc
          (n + 1) * k ≤ (3 * k) * k := Nat.mul_le_mul_right k hnprev
          _ = 3 * k ^ 2 := by ring
      have hfinite :
          (k + 2) * (2 * (((n + 1) * k) + k)) ≤
            fordMomentCoefficientExponent k (n + 1) := by
        have hnnext : n + 2 ≤ 3 * k := hn
        have hleft :
            (k + 2) * (2 * (((n + 1) * k) + k)) ≤ 20 * k ^ 3 := by
          have hrewrite : ((n + 1) * k) + k = (n + 2) * k := by ring
          rw [hrewrite]
          calc
            (k + 2) * (2 * ((n + 2) * k)) ≤
                (k + 2) * (2 * ((3 * k) * k)) := by gcongr
            _ ≤ 20 * k ^ 3 := by
              nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]
        exact hleft.trans (by unfold fordMomentCoefficientExponent; omega)
      rw [fordMomentCoefficient36_succ]
      apply fordStepGlobalCoefficient_le_universal_power_exact hk hs
          (fordMomentCoefficient36_nonneg k n) hprev
      · rw [fordMomentCoefficientExponent_succ]
      · exact hfinite

/-- The `s=2k²` moment estimate itself only requires `k ≥ 1000`; the absolute
PNT threshold is carried by the recurrence coefficient, not by the degree. -/
theorem ford_double_square_moment_bound_universal
    {k : ℕ} (hk : 1000 ≤ k) :
    FordVinogradovMomentBound (2 * k ^ 2) k
      (fordMomentCoefficient36 k (2 * k - 1))
      ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 4 + 17 / (10 * (k : ℝ)))) := by
  have hkpos : 0 < k := by omega
  have hnLower : 1 ≤ 2 * k := by omega
  have hnUpper : 2 * k ≤ k ^ 2 := by
    nlinarith [Nat.zero_le (k ^ 2)]
  have hmoment := fordLemma36_moment_bound_quantitative hk hnLower hnUpper
  have hargPos : (0 : ℝ) < 3 * (k : ℝ) / 8 := by positivity
  have hkThird : (k : ℝ) / 3 ≤ 3 * (k : ℝ) / 8 := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hlogThird : Real.log ((k : ℝ) / 3) =
      Real.log (k : ℝ) - Real.log 3 := by
    rw [Real.log_div (by positivity) (by norm_num : (3 : ℝ) ≠ 0)]
  have hlogThree : Real.log (3 : ℝ) ≤ 2 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)).trans_eq
      (by norm_num)
  have hlogArg : (49 / 10 : ℝ) < Real.log (3 * (k : ℝ) / 8) := by
    have hlogK := ford_log_k_lower hk
    have hkDivPos : (0 : ℝ) < (k : ℝ) / 3 := by positivity
    have hmono := Real.strictMonoOn_log.monotoneOn hkDivPos hargPos hkThird
    rw [hlogThird] at hmono
    linarith
  have hsource : ((2 * k : ℕ) : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 := by
    push_cast
    have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hdelta := fordLemma36_delta_exponent hk (n := 2 * k - 1)
    (by omega) (by simpa [show 2 * k - 1 + 1 = 2 * k by omega] using hsource)
  rw [show 2 * k - 1 + 1 = 2 * k by omega] at hdelta
  have hdeltaTarget : fordDeltaSequence36 k (2 * k - 1) ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 4 + 17 / (10 * (k : ℝ))) := by
    have hkR0 : (0 : ℝ) < k := by positivity
    have hExpArg :
        1 / 2 - 2 * ((2 * k : ℕ) : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ)) ≤
          1 / 2 - 4 + 17 / (10 * (k : ℝ)) := by
      push_cast
      field_simp
      nlinarith
    have hexp := Real.exp_le_exp.mpr hExpArg
    exact hdelta.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hmoment' := hmoment.mono_delta hdeltaTarget
  have hsEq : (2 * k) * k = 2 * k ^ 2 := by ring
  rw [hsEq] at hmoment'
  exact hmoment'

#print axioms fordLemma34Endpoint_le_universalBase_pow
#print axioms fordMomentCoefficient36_le_universal_sharp_power
#print axioms ford_double_square_moment_bound_universal

end

end GafniTao
