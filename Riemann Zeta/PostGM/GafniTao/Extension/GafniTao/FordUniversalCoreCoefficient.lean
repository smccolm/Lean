import GafniTao.FordUniversalCoefficientGrowth
import GafniTao.FordCoreCoefficientSharp

/-!
# Absolute rooted coefficient for every Ford degree `k ≥ 1000`
-/

namespace GafniTao

noncomputable section

theorem fordDoubleSquareCoefficient_le_universal_power
    {k : ℕ} (hk : 1000 ≤ k) :
    fordDoubleSquareCoefficient k ≤
      (fordUniversalCoefficientBase k : ℝ) ^ (31 * k ^ 3) := by
  have hsource := fordMomentCoefficient36_le_universal_sharp_power hk
    (n := 2 * k - 1) (by omega)
  have hnle : 2 * k - 1 ≤ 2 * k := Nat.sub_le _ _
  have hexponent : fordMomentCoefficientExponent k (2 * k - 1) ≤
      31 * k ^ 3 := by
    unfold fordMomentCoefficientExponent
    calc
      20 * k ^ 3 + k + (2 * k - 1) * (3 * k + k ^ 2) +
          2 * k * (2 * k - 1) * (2 * k - 1 + 1) ≤
        20 * k ^ 3 + k + (2 * k) * (3 * k + k ^ 2) +
          2 * k * (2 * k) * (2 * k) := by
            gcongr
            omega
      _ ≤ 31 * k ^ 3 := by
        nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]
  unfold fordDoubleSquareCoefficient
  exact hsource.trans (pow_le_pow_right₀
    (by exact_mod_cast (show 1 ≤ fordUniversalCoefficientBase k by
      have := fordUniversalCoefficientBase_ge_two hk
      omega) : (1 : ℝ) ≤ fordUniversalCoefficientBase k)
    hexponent)

theorem fordDoubleSquareDegree_le_universalBase_direct
    {k : ℕ} (hk : 1000 ≤ k) :
    10 * (fordDoubleSquareDegree k : ℝ) ^ 2 ≤
      (fordUniversalCoefficientBase k : ℝ) := by
  have hpoly : 50000 * k ^ 6 ≤ fordUniversalCoefficientBase k := by
    unfold fordUniversalCoefficientBase
    exact le_max_right _ _
  unfold fordDoubleSquareDegree
  have hk1 : 1 ≤ k := by omega
  have hk4to6 : k ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
  have hnat : 10 * (2 * k ^ 2) ^ 2 ≤ fordUniversalCoefficientBase k := by
    calc
      10 * (2 * k ^ 2) ^ 2 = 40 * k ^ 4 := by ring
      _ ≤ 50000 * k ^ 6 := by omega
      _ ≤ fordUniversalCoefficientBase k := hpoly
  exact_mod_cast hnat

theorem ford_four_mul_eight_pow_le_universal_two_k
    {k : ℕ} (hk : 1000 ≤ k) :
    4 * (8 : ℝ) ^ k ≤
      (fordUniversalCoefficientBase k : ℝ) ^ (2 * k) := by
  let B : ℝ := fordUniversalCoefficientBase k
  have hk1 : 1 ≤ k := by omega
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordUniversalCoefficientBase k by
      have := fordUniversalCoefficientBase_ge_two hk
      omega)
  have height : (8 : ℝ) ≤ B := by
    have hpoly : 50000 * k ^ 6 ≤ fordUniversalCoefficientBase k := by
      unfold fordUniversalCoefficientBase
      exact le_max_right _ _
    simpa [B] using (by
      exact_mod_cast (show 8 ≤ fordUniversalCoefficientBase k by
        have hkpow : 1 ≤ k ^ 6 := one_le_pow₀ hk1
        omega) : (8 : ℝ) ≤ fordUniversalCoefficientBase k)
  have hfour : (4 : ℝ) ≤ B ^ k := by
    calc
      (4 : ℝ) ≤ B := by linarith
      _ = B ^ 1 := by simp
      _ ≤ B ^ k := pow_le_pow_right₀ hBOne hk1
  have heightPow : (8 : ℝ) ^ k ≤ B ^ k :=
    pow_le_pow_left₀ (by norm_num) height _
  calc
    4 * (8 : ℝ) ^ k ≤ B ^ k * B ^ k :=
      mul_le_mul hfour heightPow (by positivity) (by positivity)
    _ = B ^ (2 * k) := by rw [← pow_add]; congr 1; omega

theorem fordScaledCoreCoefficient_le_universal_power
    {k : ℕ} (hk : 1000 ≤ k) :
    fordScaledCoreCoefficient k ≤
      (fordUniversalCoefficientBase k : ℝ) ^ (63 * k ^ 3) := by
  let B : ℝ := fordUniversalCoefficientBase k
  have hk1 : 1 ≤ k := by omega
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordUniversalCoefficientBase k by
      have := fordUniversalCoefficientBase_ge_two hk
      omega)
  have hfirst :
      (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k ≤ B ^ k :=
    pow_le_pow_left₀ (by positivity)
      (by simpa [B] using fordDoubleSquareDegree_le_universalBase_direct hk) _
  have hC := fordDoubleSquareCoefficient_le_universal_power hk
  have hCsq : fordDoubleSquareCoefficient k ^ 2 ≤ B ^ (62 * k ^ 3) := by
    calc
      fordDoubleSquareCoefficient k ^ 2 ≤ (B ^ (31 * k ^ 3)) ^ 2 :=
        pow_le_pow_left₀ (fordMomentCoefficient36_nonneg _ _)
          (by simpa [B] using hC) _
      _ = B ^ ((31 * k ^ 3) * 2) := (pow_mul B (31 * k ^ 3) 2).symm
      _ = B ^ (62 * k ^ 3) := by congr 1; ring
  have hlast : (4 * (8 : ℝ) ^ k) ^ k ≤ B ^ (2 * k ^ 2) := by
    calc
      _ ≤ (B ^ (2 * k)) ^ k := pow_le_pow_left₀ (by positivity)
        (by simpa [B] using ford_four_mul_eight_pow_le_universal_two_k hk) _
      _ = B ^ ((2 * k) * k) := (pow_mul B (2 * k) k).symm
      _ = B ^ (2 * k ^ 2) := by congr 1; ring
  have hexponent : k + 62 * k ^ 3 + 2 * k ^ 2 ≤ 63 * k ^ 3 := by
    nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]
  unfold fordScaledCoreCoefficient
  calc
    (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
        fordDoubleSquareCoefficient k ^ 2 * (4 * (8 : ℝ) ^ k) ^ k ≤
      B ^ k * B ^ (62 * k ^ 3) * B ^ (2 * k ^ 2) := by gcongr
    _ = B ^ (k + 62 * k ^ 3 + 2 * k ^ 2) := by
      rw [← pow_add, ← pow_add]
    _ ≤ B ^ (63 * k ^ 3) := pow_le_pow_right₀ hBOne hexponent

theorem fordScaledCoreCoefficient_root_le_universalBase
    {k : ℕ} (hk : 1000 ≤ k) :
    (fordScaledCoreCoefficient k) ^
        (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
      (fordUniversalCoefficientBase k : ℝ) ^ (8 / (k : ℝ)) := by
  let B : ℝ := fordUniversalCoefficientBase k
  have hk1 : 1 ≤ k := by omega
  have hmono := Real.rpow_le_rpow (fordScaledCoreCoefficient_nonneg k)
    (by simpa [B] using fordScaledCoreCoefficient_le_universal_power hk)
    (by positivity : 0 ≤ (1 / (((8 * k ^ 4 : ℕ) : ℝ))))
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordUniversalCoefficientBase k by
      have := fordUniversalCoefficientBase_ge_two hk
      omega)
  calc
    (fordScaledCoreCoefficient k) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
        (B ^ (63 * k ^ 3)) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := hmono
    _ = B ^ (63 / (8 * (k : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
      push_cast
      field_simp
    _ ≤ B ^ (8 / (k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hBOne (by
      have hkR : (0 : ℝ) < k := by positivity
      calc
        (63 : ℝ) / (8 * k) = (63 / 8 : ℝ) / k := by ring
        _ ≤ 8 / k := (div_le_div_iff_of_pos_right hkR).2 (by norm_num))

def fordUniversalRootCoefficient : ℝ :=
  (fordAbsoluteCoefficientConstant : ℝ) ^ 8 * (2 : ℝ) ^ 96

theorem fordUniversalCoefficientBase_le_absolute_mul
    {k : ℕ} (hk : 1000 ≤ k) :
    fordUniversalCoefficientBase k ≤ fordAbsoluteCoefficientConstant * k ^ 6 := by
  have hk1 : 1 ≤ k := by omega
  have hkpow : 1 ≤ k ^ 6 := one_le_pow₀ hk1
  have hAleft : fordUniformPrimeThreshold + 1 ≤ fordAbsoluteCoefficientConstant := by
    unfold fordAbsoluteCoefficientConstant
    exact le_max_left _ _
  have hAright : 50000 ≤ fordAbsoluteCoefficientConstant := by
    unfold fordAbsoluteCoefficientConstant
    exact le_max_right _ _
  unfold fordUniversalCoefficientBase
  apply max_le
  · exact hAleft.trans (by
      calc
        fordAbsoluteCoefficientConstant = fordAbsoluteCoefficientConstant * 1 := by simp
        _ ≤ fordAbsoluteCoefficientConstant * k ^ 6 :=
          Nat.mul_le_mul_left _ hkpow)
  · exact Nat.mul_le_mul_right _ hAright

theorem ford_k_pow_six_le_two_pow
    {k : ℕ} (hk : 1 ≤ k) : k ^ 6 ≤ 2 ^ (12 * k) := by
  have hsource := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
  have hktwo : k ≤ 2 ^ (2 * k) :=
    (show k ≤ 2 * k ^ 2 + 1 by
      nlinarith [Nat.zero_le (k ^ 2)]).trans hsource
  calc
    k ^ 6 ≤ (2 ^ (2 * k)) ^ 6 := by gcongr
    _ = 2 ^ (12 * k) := by
      rw [← pow_mul]
      congr 1
      ring

theorem fordScaledCoreCoefficient_root_le_absolute
    {k : ℕ} (hk : 1000 ≤ k) :
    (fordScaledCoreCoefficient k) ^
        (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤ fordUniversalRootCoefficient := by
  let U : ℝ := fordUniversalCoefficientBase k
  let A : ℝ := fordAbsoluteCoefficientConstant
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by positivity
  have hAoneNat : 1 ≤ fordAbsoluteCoefficientConstant := by
    unfold fordAbsoluteCoefficientConstant
    exact (by norm_num : 1 ≤ 50000).trans (le_max_right _ _)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    simpa [A] using (by exact_mod_cast hAoneNat :
      (1 : ℝ) ≤ fordAbsoluteCoefficientConstant)
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hbaseNat := fordUniversalCoefficientBase_le_absolute_mul hk
  have hbase : U ≤ A * (k : ℝ) ^ 6 := by
    dsimp [U, A]
    exact_mod_cast hbaseNat
  have hq0 : (0 : ℝ) ≤ 8 / (k : ℝ) := by positivity
  have hq8 : (8 / (k : ℝ)) ≤ 8 := by
    rw [div_le_iff₀ hkR]
    nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast hk1]
  have hAq : A ^ (8 / (k : ℝ)) ≤ A ^ (8 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hA1 hq8
  have hkSixNat := ford_k_pow_six_le_two_pow hk1
  have hkSix : (k : ℝ) ^ 6 ≤ (2 : ℝ) ^ (12 * k) := by
    exact_mod_cast hkSixNat
  have hkq := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 6)
    hkSix hq0
  have hbaseq := Real.rpow_le_rpow hU0 hbase hq0
  calc
    (fordScaledCoreCoefficient k) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
        U ^ (8 / (k : ℝ)) := by
      simpa [U] using fordScaledCoreCoefficient_root_le_universalBase hk
    _ ≤ (A * (k : ℝ) ^ 6) ^ (8 / (k : ℝ)) := hbaseq
    _ = A ^ (8 / (k : ℝ)) * ((k : ℝ) ^ 6) ^ (8 / (k : ℝ)) := by
      rw [Real.mul_rpow hA0 (by positivity)]
    _ ≤ A ^ (8 : ℝ) * ((2 : ℝ) ^ (12 * k)) ^ (8 / (k : ℝ)) := by
      gcongr
    _ = A ^ 8 * (2 : ℝ) ^ 96 := by
      congr 1
      · exact Real.rpow_natCast A 8
      · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        push_cast
        field_simp
        norm_num
    _ = fordUniversalRootCoefficient := rfl

#print axioms fordDoubleSquareCoefficient_le_universal_power
#print axioms fordScaledCoreCoefficient_root_le_universalBase
#print axioms fordScaledCoreCoefficient_root_le_absolute

end

end GafniTao
