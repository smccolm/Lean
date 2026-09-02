import GafniTao.FordLemma51Quantitative

/-!
# Polynomial control of the rooted Lemma 5.1 coefficient

The quantitative coefficient accumulated in the moment recurrence is made
explicit here.  Before taking the `8k⁴`-th root it is at most the
`84k⁴`-th power of `50000k⁶`; after taking the root it is at most the eleventh
power of that base.
-/

namespace GafniTao

noncomputable section

theorem fordDoubleSquareCoefficient_le_base_power
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordDoubleSquareCoefficient k ≤
      (fordCoefficientBase k : ℝ) ^ (41 * k ^ 4) := by
  have hsource := (ford_double_square_moment_quantitative hk).2
  have hbaseOneNat : 1 ≤ fordCoefficientBase k := by
    exact (fordCoefficientBase_ge_two hk).trans' (by omega)
  have hexponent : k + 20 * (2 * k - 1) * k ^ 3 ≤ 41 * k ^ 4 := by
    have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
    have hkToFourth : k ≤ k ^ 4 := by
      calc
        k = k ^ 1 := by simp
        _ ≤ k ^ 4 := pow_le_pow_right₀ (by omega : 1 ≤ k) (by omega)
    have hsub : 2 * k - 1 ≤ 2 * k := Nat.sub_le _ _
    have hmul : 20 * (2 * k - 1) * k ^ 3 ≤ 40 * k ^ 4 := by
      calc
        20 * (2 * k - 1) * k ^ 3 ≤ 20 * (2 * k) * k ^ 3 := by gcongr
        _ = 40 * k ^ 4 := by ring
    omega
  exact hsource.trans (pow_le_pow_right₀
    (by exact_mod_cast hbaseOneNat : (1 : ℝ) ≤ fordCoefficientBase k)
    hexponent)

theorem fordDoubleSquareDegree_base_le
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    10 * (fordDoubleSquareDegree k : ℝ) ^ 2 ≤
      (fordCoefficientBase k : ℝ) := by
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  unfold fordDoubleSquareDegree fordCoefficientBase
  have hpow : k ^ 4 ≤ k ^ 6 := pow_le_pow_right₀ hk1 (by omega)
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring_nf
  exact_mod_cast (show k ^ 4 * 40 ≤ k ^ 6 * 50000 by omega)

theorem ford_eight_le_coefficientBase
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    (8 : ℝ) ≤ fordCoefficientBase k := by
  have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
  unfold fordCoefficientBase
  have hk1 : 1 ≤ k := by omega
  have hkpow : 1 ≤ k ^ 6 := one_le_pow₀ hk1
  exact_mod_cast (show 8 ≤ 50000 * k ^ 6 by omega)

theorem ford_four_mul_eight_pow_le_base_two_k
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    4 * (8 : ℝ) ^ k ≤
      (fordCoefficientBase k : ℝ) ^ (2 * k) := by
  let B : ℝ := fordCoefficientBase k
  have hk1000 := fordCoefficientKThreshold_ge_thousand.trans hk
  have hk1 : 1 ≤ k := by omega
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordCoefficientBase k by
      exact (fordCoefficientBase_ge_two hk).trans' (by omega))
  have hfour : (4 : ℝ) ≤ B ^ k := by
    calc
      (4 : ℝ) ≤ B := by
        have := ford_eight_le_coefficientBase hk
        dsimp [B]
        linarith
      _ = B ^ 1 := by simp
      _ ≤ B ^ k := pow_le_pow_right₀ hBOne hk1
  have height : (8 : ℝ) ^ k ≤ B ^ k :=
    pow_le_pow_left₀ (by norm_num) (by simpa [B] using ford_eight_le_coefficientBase hk) _
  calc
    4 * (8 : ℝ) ^ k ≤ B ^ k * B ^ k :=
      mul_le_mul hfour height (by positivity) (by positivity)
    _ = B ^ (2 * k) := by rw [← pow_add]; congr 1; omega

theorem fordScaledCoreCoefficient_le_base_power
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    fordScaledCoreCoefficient k ≤
      (fordCoefficientBase k : ℝ) ^ (84 * k ^ 4) := by
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
      (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k ≤ B ^ (k ^ 4) := by
    calc
      _ ≤ B ^ k := pow_le_pow_left₀ (by positivity) hfirstBase _
      _ ≤ B ^ (k ^ 4) := pow_le_pow_right₀ hBOne (by
        calc
          k = k ^ 1 := by simp
          _ ≤ k ^ 4 := pow_le_pow_right₀ hk1 (by omega))
  have hC := fordDoubleSquareCoefficient_le_base_power hk
  have hCsq : fordDoubleSquareCoefficient k ^ 2 ≤ B ^ (82 * k ^ 4) := by
    calc
      fordDoubleSquareCoefficient k ^ 2 ≤ (B ^ (41 * k ^ 4)) ^ 2 :=
        pow_le_pow_left₀ (fordMomentCoefficient36_nonneg _ _) (by simpa [B] using hC) _
      _ = B ^ ((41 * k ^ 4) * 2) := (pow_mul B (41 * k ^ 4) 2).symm
      _ = B ^ (82 * k ^ 4) := by congr 1; ring
  have hlastBase : 4 * (8 : ℝ) ^ k ≤ B ^ (2 * k) := by
    simpa [B] using ford_four_mul_eight_pow_le_base_two_k hk
  have hlast : (4 * (8 : ℝ) ^ k) ^ k ≤ B ^ (k ^ 4) := by
    calc
      _ ≤ (B ^ (2 * k)) ^ k := pow_le_pow_left₀ (by positivity) hlastBase _
      _ = B ^ ((2 * k) * k) := (pow_mul B (2 * k) k).symm
      _ = B ^ (2 * k ^ 2) := by congr 1; ring
      _ ≤ B ^ (k ^ 4) := pow_le_pow_right₀ hBOne (by
        have hkSq : 2 ≤ k ^ 2 := by nlinarith [Nat.zero_le (k ^ 2)]
        nlinarith [Nat.zero_le (k ^ 2), Nat.zero_le (k ^ 4)])
  unfold fordScaledCoreCoefficient
  calc
    (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
        fordDoubleSquareCoefficient k ^ 2 *
        (4 * (8 : ℝ) ^ k) ^ k ≤
      B ^ (k ^ 4) * B ^ (82 * k ^ 4) * B ^ (k ^ 4) := by
        gcongr
    _ = B ^ (84 * k ^ 4) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem fordScaledCoreCoefficient_root_le
    {k : ℕ} (hk : fordCoefficientKThreshold ≤ k) :
    (fordScaledCoreCoefficient k) ^
        (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
      (fordCoefficientBase k : ℝ) ^ 11 := by
  let B : ℝ := fordCoefficientBase k
  have hk1 : 1 ≤ k := by
    exact (show 1 ≤ fordCoefficientKThreshold by
      exact le_trans (by norm_num) fordCoefficientKThreshold_ge_thousand).trans hk
  have hcoeff0 := fordScaledCoreCoefficient_nonneg k
  have hq0 : 0 ≤ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := by positivity
  have hmono := Real.rpow_le_rpow hcoeff0
    (by simpa [B] using fordScaledCoreCoefficient_le_base_power hk) hq0
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBOne : 1 ≤ B := by
    dsimp [B]
    exact_mod_cast (show 1 ≤ fordCoefficientBase k by
      exact (fordCoefficientBase_ge_two hk).trans' (by omega))
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  calc
    (fordScaledCoreCoefficient k) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) ≤
        (B ^ (84 * k ^ 4)) ^ (1 / (((8 * k ^ 4 : ℕ) : ℝ))) := hmono
    _ = B ^ (21 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
      push_cast
      field_simp
      ring
    _ ≤ B ^ (11 : ℝ) := Real.rpow_le_rpow_of_exponent_le hBOne (by norm_num)
    _ = B ^ 11 := by norm_num

#print axioms fordDoubleSquareCoefficient_le_base_power
#print axioms fordScaledCoreCoefficient_le_base_power
#print axioms fordScaledCoreCoefficient_root_le

end

end GafniTao
