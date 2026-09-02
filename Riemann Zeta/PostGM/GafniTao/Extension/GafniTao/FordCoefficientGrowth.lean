import GafniTao.FordLemma36QuantitativeMoment
import GafniTao.FordTheorem3Exponent

/-!
# Polynomial growth of Ford's quantitative moment coefficient

For the later application only the band `s ≤ 3 k²` is needed.  On this band
the fixed PNT constant is dominated once `k` passes one fixed threshold, the
Lemma 3.4 endpoint is at most a stated power of `50000 k⁶`, and the complete
coefficient recurrence has a polynomial-power majorant.
-/

namespace GafniTao

noncomputable section

def fordCoefficientKThreshold : ℕ :=
  max 1000 fordUniformPrimeThreshold

def fordCoefficientBase (k : ℕ) : ℕ :=
  50000 * k ^ 6

theorem fordCoefficientKThreshold_ge_thousand :
    1000 ≤ fordCoefficientKThreshold := le_max_left _ _

theorem fordCoefficientKThreshold_ge_prime :
    fordUniformPrimeThreshold ≤ fordCoefficientKThreshold := le_max_right _ _

theorem fordCoefficientBase_ge_two
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    2 ≤ fordCoefficientBase k := by
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  unfold fordCoefficientBase
  have : 1 ≤ k ^ 6 := one_le_pow₀ hk1
  omega

theorem fordPrimePacketScaleThreshold_le_coefficientBase
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordPrimePacketScaleThreshold k ≤ fordCoefficientBase k := by
  have hprime : fordUniformPrimeThreshold ≤ k :=
    fordCoefficientKThreshold_ge_prime.trans hk
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  unfold fordPrimePacketScaleThreshold fordCoefficientBase
  apply max_le
  · exact hprime.trans (by
      calc
        k = k ^ 1 := by simp
        _ ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
        _ ≤ 50000 * k ^ 6 := Nat.le_mul_of_pos_left _ (by norm_num))
  · calc
      (200 * k ^ 3) ^ 2 = 40000 * k ^ 6 := by ring
      _ ≤ 50000 * k ^ 6 := Nat.mul_le_mul_right _ (by norm_num)

theorem fordLemma34UniformBase_le_coefficientBase
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordLemma34UniformBase k ≤ (fordCoefficientBase k : ℝ) := by
  unfold fordLemma34UniformBase
  apply max_le
  · exact_mod_cast (show k ≤ fordCoefficientBase k by
      have hk1 : 1 ≤ k := by
        exact (show 1 ≤ fordCoefficientKThreshold by
          exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
      unfold fordCoefficientBase
      calc
        k = k ^ 1 := by simp
        _ ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
        _ ≤ 50000 * k ^ 6 := Nat.le_mul_of_pos_left _ (by norm_num))
  · exact_mod_cast (show fordPrimePacketScaleThreshold k + 1 ≤
        fordCoefficientBase k by
      have hprime : fordUniformPrimeThreshold ≤ k :=
        fordCoefficientKThreshold_ge_prime.trans hk
      have hk1 : 1 ≤ k := by
        exact (show 1 ≤ fordCoefficientKThreshold by
          exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
      have hkToSix : k ≤ k ^ 6 := by
        calc
          k = k ^ 1 := by simp
          _ ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
      have hstrong : fordPrimePacketScaleThreshold k ≤ 40000 * k ^ 6 := by
        unfold fordPrimePacketScaleThreshold
        apply max_le
        · exact hprime.trans (hkToSix.trans
            (Nat.le_mul_of_pos_left _ (by norm_num)))
        · calc
            (200 * k ^ 3) ^ 2 = 40000 * k ^ 6 := by ring
            _ ≤ 40000 * k ^ 6 := le_rfl
      unfold fordCoefficientBase
      have hroom : fordPrimePacketScaleThreshold k + 1 ≤
          50000 * k ^ 6 := by
        have hpow : 1 ≤ k ^ 6 := one_le_pow₀ hk1
        omega
      exact hroom)

/-- Quantitative upper bound for the integral Lemma 3.4 endpoint throughout
the moment band used later. -/
theorem fordLemma34Endpoint_le_coefficientBase_pow
    {s k : ℕ} (hk : fordCoefficientKThreshold ≤ k) (hs : s ≤ 3 * k ^ 2) :
    fordLemma34Endpoint s k ≤ fordCoefficientBase k ^ (k + 2) := by
  have hk1000 : 1000 ≤ k := fordCoefficientKThreshold_ge_thousand.trans hk
  have hBtwo := fordCoefficientBase_ge_two hk
  have hBone : 1 ≤ fordCoefficientBase k := by omega
  have huniform := fordLemma34UniformBase_le_coefficientBase hk
  have hfirstNat : 4 * k ^ 4 + 2 ≤ fordCoefficientBase k := by
    unfold fordCoefficientBase
    have hk1 : 1 ≤ k := by omega
    have hk4to6 : k ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
    have hk6 : 1 ≤ k ^ 6 := one_le_pow₀ hk1
    omega
  have hsourceNat : 64 * s ^ 2 + 1 ≤ fordCoefficientBase k := by
    unfold fordCoefficientBase
    have hsSq : s ^ 2 ≤ (3 * k ^ 2) ^ 2 := Nat.pow_le_pow_left hs 2
    have hsSq' : s ^ 2 ≤ 9 * k ^ 4 := by
      calc
        s ^ 2 ≤ (3 * k ^ 2) ^ 2 := hsSq
        _ = 9 * k ^ 4 := by ring
    have hk1 : 1 ≤ k := by omega
    have hk4to6 : k ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
    have hk6 : 1 ≤ k ^ 6 := one_le_pow₀ hk1
    omega
  apply Nat.ceil_le.mpr
  unfold fordLemma34ExplicitThreshold
  apply max_le
  · have hcast : (((4 * k ^ 4 + 2 : ℕ) : ℝ)) ≤
        (fordCoefficientBase k : ℝ) := by exact_mod_cast hfirstNat
    exact hcast.trans (by
      exact_mod_cast (show fordCoefficientBase k ≤
          fordCoefficientBase k ^ (k + 2) by
        calc
          fordCoefficientBase k = fordCoefficientBase k ^ 1 := by simp
          _ ≤ fordCoefficientBase k ^ (k + 2) :=
            pow_le_pow_right₀ hBone (by omega)))
  · apply max_le
    · have hpow := pow_le_pow_left₀
        (zero_le_one.trans (fordLemma34UniformBase_one_le k)) huniform (k + 1)
      exact hpow.trans (by
        exact_mod_cast (pow_le_pow_right₀ hBone (by omega : k + 1 ≤ k + 2)))
    · have hsourceReal : (((64 * s ^ 2 + 1 : ℕ) : ℝ)) ≤
          (fordCoefficientBase k : ℝ) := by exact_mod_cast hsourceNat
      have hpow := pow_le_pow_left₀ (by positivity) hsourceReal 10
      exact hpow.trans (by
        exact_mod_cast (pow_le_pow_right₀ hBone (by omega : 10 ≤ k + 2)))

theorem fordCoefficientBase_real_ge_k
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    (k : ℝ) ≤ (fordCoefficientBase k : ℝ) := by
  exact_mod_cast (show k ≤ fordCoefficientBase k by
    have hk1 : 1 ≤ k := by
      exact (show 1 ≤ fordCoefficientKThreshold by
        exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
    unfold fordCoefficientBase
    calc
      k = k ^ 1 := by simp
      _ ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
      _ ≤ 50000 * k ^ 6 := Nat.le_mul_of_pos_left _ (by norm_num))

theorem fordCoefficientBase_real_ge_eta
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    (53 / 50 : ℝ) ≤ (fordCoefficientBase k : ℝ) := by
  have hBtwo := fordCoefficientBase_ge_two hk
  have hBtwoReal : (2 : ℝ) ≤ (fordCoefficientBase k : ℝ) := by exact_mod_cast hBtwo
  exact (by norm_num : (53 / 50 : ℝ) ≤ 2).trans hBtwoReal

/-- A single recurrence step costs at most `20 k³` powers of the polynomial
base on the range used in the later `s=2k²` specialization. -/
theorem fordStepGlobalCoefficient_le_power
    {s k : ℕ} {C : ℝ} {E : ℕ}
    (hk : fordCoefficientKThreshold ≤ k) (hs : s ≤ 3 * k ^ 2)
    (hC0 : 0 ≤ C) (hC : C ≤ (fordCoefficientBase k : ℝ) ^ E) :
    fordStepGlobalCoefficient s k C ≤
      (fordCoefficientBase k : ℝ) ^ (E + 20 * k ^ 3) := by
  let B : ℝ := fordCoefficientBase k
  have hBtwoNat := fordCoefficientBase_ge_two hk
  have hBoneNat : 1 ≤ fordCoefficientBase k := by omega
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by
    change (1 : ℝ) ≤ (fordCoefficientBase k : ℝ)
    exact_mod_cast hBoneNat
  have hkB : (k : ℝ) ≤ B := by
    simpa [B] using fordCoefficientBase_real_ge_k hk
  have hetaB : (53 / 50 : ℝ) ≤ B := by
    simpa [B] using fordCoefficientBase_real_ge_eta hk
  have haNat : 3 * k + (4 * s + k ^ 2) ≤ 20 * k ^ 3 := by
    have hs' : 4 * s ≤ 12 * k ^ 2 := by
      omega
    have hk1000 : 1000 ≤ k := fordCoefficientKThreshold_ge_thousand.trans hk
    have hkSqCube : k ^ 2 ≤ k ^ 3 := by
      calc
        k ^ 2 = k ^ 2 * 1 := by ring
        _ ≤ k ^ 2 * k := Nat.mul_le_mul_left _ (by omega)
        _ = k ^ 3 := by ring
    have hkToSq : k ≤ k ^ 2 := by
      calc
        k = k * 1 := by simp
        _ ≤ k * k := Nat.mul_le_mul_left k (by omega)
        _ = k ^ 2 := by ring
    omega
  have hstepFactor :
      (k : ℝ) ^ (3 * k) *
          (53 / 50 : ℝ) ^ (4 * (s : ℝ) + (k : ℝ) ^ 2) ≤
        B ^ (20 * k ^ 3) := by
    have hexpCast : 4 * (s : ℝ) + (k : ℝ) ^ 2 =
        ((4 * s + k ^ 2 : ℕ) : ℝ) := by norm_num
    rw [hexpCast, Real.rpow_natCast]
    calc
      (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * s + k ^ 2) ≤
          B ^ (3 * k) * B ^ (4 * s + k ^ 2) := by gcongr
      _ = B ^ (3 * k + (4 * s + k ^ 2)) :=
        (pow_add B (3 * k) (4 * s + k ^ 2)).symm
      _ ≤ B ^ (20 * k ^ 3) := pow_le_pow_right₀ hB1 haNat
  have hstep : fordStepCoefficient35 s k C (53 / 50 : ℝ) ≤
      B ^ (E + 20 * k ^ 3) := by
    unfold fordStepCoefficient35
    calc
      ((k : ℝ) ^ (3 * k) *
          (53 / 50 : ℝ) ^ (4 * (s : ℝ) + (k : ℝ) ^ 2)) * C ≤
          B ^ (20 * k ^ 3) * B ^ E := by
        exact mul_le_mul hstepFactor hC hC0
          (pow_nonneg hB0 _)
      _ = B ^ (E + 20 * k ^ 3) := by
        rw [add_comm E, pow_add]
  have hendpoint := fordLemma34Endpoint_le_coefficientBase_pow hk hs
  have hfinite : ((fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k))) ≤
      B ^ (E + 20 * k ^ 3) := by
    have hendpointReal : (fordLemma34Endpoint s k : ℝ) ≤ B ^ (k + 2) := by
      change (fordLemma34Endpoint s k : ℝ) ≤
        (fordCoefficientBase k : ℝ) ^ (k + 2)
      exact_mod_cast hendpoint
    have hpow := pow_le_pow_left₀ (by positivity) hendpointReal (2 * (s + k))
    have hbNat : (k + 2) * (2 * (s + k)) ≤ 20 * k ^ 3 := by
      have hk1000 : 1000 ≤ k := fordCoefficientKThreshold_ge_thousand.trans hk
      have hs' : s + k ≤ 3 * k ^ 2 + k := Nat.add_le_add_right hs k
      have hkSqCube : k ^ 2 ≤ k ^ 3 := by
        calc
          k ^ 2 = k ^ 2 * 1 := by ring
          _ ≤ k ^ 2 * k := Nat.mul_le_mul_left _ (by omega)
          _ = k ^ 3 := by ring
      nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]
    calc
      (fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k)) ≤
          (B ^ (k + 2)) ^ (2 * (s + k)) := hpow
      _ = B ^ ((k + 2) * (2 * (s + k))) :=
        (pow_mul B (k + 2) (2 * (s + k))).symm
      _ ≤ B ^ (20 * k ^ 3) := pow_le_pow_right₀ hB1 hbNat
      _ ≤ B ^ (E + 20 * k ^ 3) :=
        pow_le_pow_right₀ hB1 (by omega)
  exact max_le hstep hfinite

theorem fordMomentCoefficient36_nonneg (k n : ℕ) :
    0 ≤ fordMomentCoefficient36 k n := by
  induction n with
  | zero => simp
  | succ n _ih =>
      rw [fordMomentCoefficient36_succ]
      unfold fordStepGlobalCoefficient
      exact (by positivity : 0 ≤
        ((fordLemma34Endpoint ((n + 1) * k) k : ℝ) ^
          (2 * (((n + 1) * k) + k)))).trans (le_max_right _ _)

/-- The exponent obtained by paying the finite-prefix maximum once and then
accumulating the exact analytic factors in the Lemma 3.5 recurrence. -/
def fordMomentCoefficientExponent (k n : ℕ) : ℕ :=
  20 * k ^ 3 + k + n * (3 * k + k ^ 2) + 2 * k * n * (n + 1)

@[simp] theorem fordMomentCoefficientExponent_zero (k : ℕ) :
    fordMomentCoefficientExponent k 0 = 20 * k ^ 3 + k := by
  simp [fordMomentCoefficientExponent]

theorem fordMomentCoefficientExponent_succ (k n : ℕ) :
    fordMomentCoefficientExponent k (n + 1) =
      fordMomentCoefficientExponent k n +
        (3 * k + (4 * ((n + 1) * k) + k ^ 2)) := by
  unfold fordMomentCoefficientExponent
  ring

/-- A recurrence step with its analytic and finite-prefix exponents kept
separate.  Unlike `fordStepGlobalCoefficient_le_power`, this theorem does not
charge the finite-prefix exponent on every iteration. -/
theorem fordStepGlobalCoefficient_le_power_exact
    {s k : ℕ} {C : ℝ} {E E' : ℕ}
    (hk : fordCoefficientKThreshold ≤ k) (hs : s ≤ 3 * k ^ 2)
    (hC0 : 0 ≤ C) (hC : C ≤ (fordCoefficientBase k : ℝ) ^ E)
    (hstepExp : E + (3 * k + (4 * s + k ^ 2)) ≤ E')
    (hfiniteExp : (k + 2) * (2 * (s + k)) ≤ E') :
    fordStepGlobalCoefficient s k C ≤
      (fordCoefficientBase k : ℝ) ^ E' := by
  let B : ℝ := fordCoefficientBase k
  have hBtwoNat := fordCoefficientBase_ge_two hk
  have hBoneNat : 1 ≤ fordCoefficientBase k := by omega
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := by
    change (1 : ℝ) ≤ (fordCoefficientBase k : ℝ)
    exact_mod_cast hBoneNat
  have hkB : (k : ℝ) ≤ B := by
    simpa [B] using fordCoefficientBase_real_ge_k hk
  have hetaB : (53 / 50 : ℝ) ≤ B := by
    simpa [B] using fordCoefficientBase_real_ge_eta hk
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
        exact mul_le_mul hstepFactor hC hC0
          (pow_nonneg hB0 _)
      _ = B ^ (E + (3 * k + (4 * s + k ^ 2))) := by
        rw [add_comm E, ← pow_add]
      _ ≤ B ^ E' := pow_le_pow_right₀ hB1 hstepExp
  have hendpoint := fordLemma34Endpoint_le_coefficientBase_pow hk hs
  have hfinite : ((fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k))) ≤
      B ^ E' := by
    have hendpointReal : (fordLemma34Endpoint s k : ℝ) ≤ B ^ (k + 2) := by
      change (fordLemma34Endpoint s k : ℝ) ≤
        (fordCoefficientBase k : ℝ) ^ (k + 2)
      exact_mod_cast hendpoint
    have hpow := pow_le_pow_left₀ (by positivity) hendpointReal (2 * (s + k))
    calc
      (fordLemma34Endpoint s k : ℝ) ^ (2 * (s + k)) ≤
          (B ^ (k + 2)) ^ (2 * (s + k)) := hpow
      _ = B ^ ((k + 2) * (2 * (s + k))) :=
        (pow_mul B (k + 2) (2 * (s + k))).symm
      _ ≤ B ^ E' := pow_le_pow_right₀ hB1 hfiniteExp
  exact max_le hstep hfinite

/-- Source-scale `O(k³)` bound for the exact Lemma 3.6 moment coefficient. -/
theorem fordMomentCoefficient36_le_sharp_power
    {k n : ℕ} (hk : fordCoefficientKThreshold ≤ k) (hn : n + 1 ≤ 3 * k) :
    fordMomentCoefficient36 k n ≤
      (fordCoefficientBase k : ℝ) ^ fordMomentCoefficientExponent k n := by
  induction n with
  | zero =>
      rw [fordMomentCoefficient36_zero]
      have hfac : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
      have hkB := fordCoefficientBase_real_ge_k hk
      have hB1 : (1 : ℝ) ≤ fordCoefficientBase k := by
        exact_mod_cast (show 1 ≤ fordCoefficientBase k by
          exact (fordCoefficientBase_ge_two hk).trans' (by omega))
      calc
        (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast hfac
        _ = (k : ℝ) ^ k := by norm_num
        _ ≤ (fordCoefficientBase k : ℝ) ^ k :=
          pow_le_pow_left₀ (by positivity) hkB k
        _ ≤ (fordCoefficientBase k : ℝ) ^ fordMomentCoefficientExponent k 0 :=
          pow_le_pow_right₀ hB1 (by
            simp [fordMomentCoefficientExponent])
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
        have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
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
        exact hleft.trans (by
          unfold fordMomentCoefficientExponent
          omega)
      rw [fordMomentCoefficient36_succ]
      apply fordStepGlobalCoefficient_le_power_exact hk hs
          (fordMomentCoefficient36_nonneg k n) hprev
      · rw [fordMomentCoefficientExponent_succ]
      · exact hfinite

/-- Closed polynomial-power bound for the exact coefficient recurrence. -/
theorem fordMomentCoefficient36_le_power
    {k n : ℕ} (hk : fordCoefficientKThreshold ≤ k) (hn : n + 1 ≤ 3 * k) :
    fordMomentCoefficient36 k n ≤
      (fordCoefficientBase k : ℝ) ^ (k + 20 * n * k ^ 3) := by
  induction n with
  | zero =>
      rw [fordMomentCoefficient36_zero]
      have hfac : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
      have hkB := fordCoefficientBase_real_ge_k hk
      calc
        (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast hfac
        _ = (k : ℝ) ^ k := by norm_num
        _ ≤ (fordCoefficientBase k : ℝ) ^ k :=
          pow_le_pow_left₀ (by positivity) hkB k
        _ = (fordCoefficientBase k : ℝ) ^ (k + 20 * 0 * k ^ 3) := by simp
  | succ n ih =>
      have hnprev : n + 1 ≤ 3 * k := by omega
      have hprev := ih hnprev
      have hs : (n + 1) * k ≤ 3 * k ^ 2 := by
        calc
          (n + 1) * k ≤ (3 * k) * k := Nat.mul_le_mul_right k hnprev
          _ = 3 * k ^ 2 := by ring
      rw [fordMomentCoefficient36_succ]
      have hstep := fordStepGlobalCoefficient_le_power hk hs
        (fordMomentCoefficient36_nonneg k n) hprev
      convert hstep using 1
      all_goals ring

/-- The quantitative moment theorem in the single `s=2k²` specialization
needed for the complete-window Lemma 5.1 application. -/
theorem ford_double_square_moment_quantitative
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    FordVinogradovMomentBound (2 * k ^ 2) k
      (fordMomentCoefficient36 k (2 * k - 1))
      ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
        (1 / 2 - 4 + 17 / (10 * (k : ℝ)))) ∧
    fordMomentCoefficient36 k (2 * k - 1) ≤
      (fordCoefficientBase k : ℝ) ^
        (k + 20 * (2 * k - 1) * k ^ 3) := by
  have hk1000 : 1000 ≤ k := fordCoefficientKThreshold_ge_thousand.trans hk
  have hkpos : 0 < k := by omega
  have hnLower : 1 ≤ 2 * k := by omega
  have hnUpper : 2 * k ≤ k ^ 2 := by
    have : 2 ≤ k := by omega
    nlinarith [Nat.zero_le (k ^ 2)]
  have hmoment := fordLemma36_moment_bound_quantitative hk1000 hnLower hnUpper
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
    have hlogK := ford_log_k_lower hk1000
    have hkDivPos : (0 : ℝ) < (k : ℝ) / 3 := by positivity
    have hmono := Real.strictMonoOn_log.monotoneOn hkDivPos hargPos hkThird
    rw [hlogThird] at hmono
    linarith
  have hsource : ((2 * k : ℕ) : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 := by
    push_cast
    have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk1000
    nlinarith
  have hdelta := fordLemma36_delta_exponent hk1000 (n := 2 * k - 1)
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
  have hcoeff := fordMomentCoefficient36_le_power hk
    (n := 2 * k - 1) (by omega)
  have hsEq : (2 * k) * k = 2 * k ^ 2 := by ring
  rw [hsEq] at hmoment'
  exact ⟨hmoment', hcoeff⟩

#print axioms fordPrimePacketScaleThreshold_le_coefficientBase
#print axioms fordLemma34UniformBase_le_coefficientBase
#print axioms fordLemma34Endpoint_le_coefficientBase_pow
#print axioms fordStepGlobalCoefficient_le_power
#print axioms fordMomentCoefficient36_le_power
#print axioms ford_double_square_moment_quantitative

end

end GafniTao
