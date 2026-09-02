import GafniTao.FordCoreCoefficientBound

/-!
# Source-scale control of the rooted Lemma 5.1 coefficient

The earlier polynomial bound deliberately paid the finite-prefix repair at
every recurrence step and therefore produced an `O(k⁴)` exponent.  The exact
recurrence is a maximum.  Using `fordMomentCoefficientExponent` pays that
repair once and accumulates only the analytic step factors, giving the
source-scale `O(k³)` exponent required before the `8k⁴`-th root.
-/

namespace GafniTao

noncomputable section

theorem fordDoubleSquareCoefficient_le_sharp_base_power
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordDoubleSquareCoefficient k ≤
      (fordCoefficientBase k : ℝ) ^ (31 * k ^ 3) := by
  have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
  have hkpos : 0 < k := by omega
  have hsource := fordMomentCoefficient36_le_sharp_power hk
    (n := 2 * k - 1) (by omega)
  have hnle : 2 * k - 1 ≤ 2 * k := Nat.sub_le _ _
  have hnEq : 2 * k - 1 + 1 = 2 * k := by omega
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
    (by exact_mod_cast (show 1 ≤ fordCoefficientBase k by
      exact (fordCoefficientBase_ge_two hk).trans' (by omega)) :
      (1 : ℝ) ≤ fordCoefficientBase k)
    hexponent)

theorem fordScaledCoreCoefficient_le_sharp_base_power
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordScaledCoreCoefficient k ≤
      (fordCoefficientBase k : ℝ) ^ (63 * k ^ 3) := by
  let B : ℝ := fordCoefficientBase k
  have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
  have hk1 : 1 ≤ k := by omega
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordCoefficientBase k by
      exact (fordCoefficientBase_ge_two hk).trans' (by omega))
  have hfirstBase :
      10 * (fordDoubleSquareDegree k : ℝ) ^ 2 ≤ B := by
    simpa [B] using fordDoubleSquareDegree_base_le hk
  have hfirst :
      (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k ≤ B ^ k :=
    pow_le_pow_left₀ (by positivity) hfirstBase _
  have hC := fordDoubleSquareCoefficient_le_sharp_base_power hk
  have hCsq : fordDoubleSquareCoefficient k ^ 2 ≤ B ^ (62 * k ^ 3) := by
    calc
      fordDoubleSquareCoefficient k ^ 2 ≤ (B ^ (31 * k ^ 3)) ^ 2 :=
        pow_le_pow_left₀ (fordMomentCoefficient36_nonneg _ _)
          (by simpa [B] using hC) _
      _ = B ^ ((31 * k ^ 3) * 2) :=
        (pow_mul B (31 * k ^ 3) 2).symm
      _ = B ^ (62 * k ^ 3) := by congr 1; ring
  have hlastBase : 4 * (8 : ℝ) ^ k ≤ B ^ (2 * k) := by
    simpa [B] using ford_four_mul_eight_pow_le_base_two_k hk
  have hlast : (4 * (8 : ℝ) ^ k) ^ k ≤ B ^ (2 * k ^ 2) := by
    calc
      _ ≤ (B ^ (2 * k)) ^ k :=
        pow_le_pow_left₀ (by positivity) hlastBase _
      _ = B ^ ((2 * k) * k) := (pow_mul B (2 * k) k).symm
      _ = B ^ (2 * k ^ 2) := by congr 1; ring
  have hexponent : k + 62 * k ^ 3 + 2 * k ^ 2 ≤ 63 * k ^ 3 := by
    nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 3)]
  unfold fordScaledCoreCoefficient
  calc
    (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
        fordDoubleSquareCoefficient k ^ 2 *
        (4 * (8 : ℝ) ^ k) ^ k ≤
      B ^ k * B ^ (62 * k ^ 3) * B ^ (2 * k ^ 2) := by
        gcongr
    _ = B ^ (k + 62 * k ^ 3 + 2 * k ^ 2) := by
      rw [← pow_add, ← pow_add]
    _ ≤ B ^ (63 * k ^ 3) := pow_le_pow_right₀ hBOne hexponent

theorem fordScaledCoreCoefficient_root_le_sharp
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    (fordScaledCoreCoefficient k) ^
        (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
      (fordCoefficientBase k : ℝ) ^ (8 / (k : ℝ)) := by
  let B : ℝ := fordCoefficientBase k
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  have hcoeff0 := fordScaledCoreCoefficient_nonneg k
  have hq0 : 0 ≤ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := by positivity
  have hmono := Real.rpow_le_rpow hcoeff0
    (by simpa [B] using fordScaledCoreCoefficient_le_sharp_base_power hk) hq0
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordCoefficientBase k by
      exact (fordCoefficientBase_ge_two hk).trans' (by omega))
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  calc
    (fordScaledCoreCoefficient k) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
        (B ^ (63 * k ^ 3)) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := hmono
    _ = B ^ (63 / (8 * (k : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
      push_cast
      field_simp
    _ ≤ B ^ (8 / (k : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hBOne (by
        have hkR : (0 : ℝ) < k := by positivity
        calc
          (63 : ℝ) / (8 * k) = (63 / 8 : ℝ) / k := by ring
          _ ≤ 8 / k := (div_le_div_iff_of_pos_right hkR).2 (by norm_num))

theorem fordCoefficientBase_le_two_pow
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordCoefficientBase k ≤ 2 ^ (16 * k) := by
  have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
  have hkpos : 0 < k := by omega
  have h50000 : 50000 ≤ k ^ 2 := by
    nlinarith [Nat.zero_le (k ^ 2)]
  have hbase : fordCoefficientBase k ≤ k ^ 8 := by
    unfold fordCoefficientBase
    calc
      50000 * k ^ 6 ≤ k ^ 2 * k ^ 6 := Nat.mul_le_mul_right _ h50000
      _ = k ^ 8 := by ring
  have hktwo : k ≤ 2 ^ (2 * k) := by
    have hsource := Nat.two_mul_sq_add_one_le_two_pow_two_mul k
    exact (show k ≤ 2 * k ^ 2 + 1 by
      nlinarith [Nat.zero_le (k ^ 2)]).trans hsource
  calc
    fordCoefficientBase k ≤ k ^ 8 := hbase
    _ ≤ (2 ^ (2 * k)) ^ 8 := by gcongr
    _ = 2 ^ (16 * k) := by
      rw [← pow_mul]
      congr 1
      ring

/-- After the literal `8k⁴`-th root the complete recurrence coefficient is
bounded by one absolute constant.  The deliberately generous `2^128` avoids
any hidden dependence on the Ford degree parameter. -/
theorem fordScaledCoreCoefficient_root_le_uniform
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    (fordScaledCoreCoefficient k) ^
        (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤ (2 : ℝ) ^ 128 := by
  let B : ℝ := fordCoefficientBase k
  have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
  have hkpos : 0 < k := by
    omega
  have hkR : (0 : ℝ) < k := by positivity
  have hbaseNat := fordCoefficientBase_le_two_pow hk
  have hbase : B ≤ (2 : ℝ) ^ (16 * k) := by
    dsimp [B]
    exact_mod_cast hbaseNat
  have hq0 : (0 : ℝ) ≤ 8 / (k : ℝ) := by positivity
  have hmono := Real.rpow_le_rpow (by dsimp [B]; positivity) hbase hq0
  calc
    (fordScaledCoreCoefficient k) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
        B ^ (8 / (k : ℝ)) := fordScaledCoreCoefficient_root_le_sharp hk
    _ ≤ ((2 : ℝ) ^ (16 * k)) ^ (8 / (k : ℝ)) := hmono
    _ = (2 : ℝ) ^ 128 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      field_simp
      norm_num

#print axioms fordMomentCoefficient36_le_sharp_power
#print axioms fordDoubleSquareCoefficient_le_sharp_base_power
#print axioms fordScaledCoreCoefficient_le_sharp_base_power
#print axioms fordScaledCoreCoefficient_root_le_sharp
#print axioms fordScaledCoreCoefficient_root_le_uniform

end

end GafniTao
