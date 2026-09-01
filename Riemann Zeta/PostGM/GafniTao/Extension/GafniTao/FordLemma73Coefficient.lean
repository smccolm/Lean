import GafniTao.FordRiemannLemma73

/-!
# The numerical coefficient in Ford Lemma 7.3

All decimal comparisons below are rational inequalities.  The only
transcendental input is a finite Taylor upper certificate for `exp (3/10)`,
used to prove `23/10 < log 10`.
-/

namespace GafniTao

noncomputable section

theorem exp_three_tenths_lt_one_point_three_five :
    Real.exp (3 / 10 : ℝ) < 1.35 := by
  have h := real_exp_le_fordExpTaylorUpper
    (n := 8) (x := (3 / 10 : ℝ)) (by norm_num) (by norm_num)
  have hTaylor : fordExpTaylorUpper 8 (3 / 10 : ℝ) < 1.35 := by
    norm_num [fordExpTaylorUpper, Finset.sum_range_succ]
  exact h.trans_lt hTaylor

theorem twenty_three_tenths_lt_log_ten :
    (23 / 10 : ℝ) < Real.log 10 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 10)]
  have hOne : Real.exp 1 < 2.719 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have hThree := exp_three_tenths_lt_one_point_three_five
  rw [show (23 / 10 : ℝ) = 1 + 1 + 3 / 10 by norm_num,
    Real.exp_add, Real.exp_add]
  have hOnePos := Real.exp_pos 1
  have hThreePos := Real.exp_pos (3 / 10 : ℝ)
  nlinarith

theorem two_hundred_thirty_le_log_of_ten_pow_hundred_le
    {t : ℝ} (ht : (10 : ℝ) ^ 100 ≤ t) :
    230 ≤ Real.log t := by
  have htenPowPos : 0 < (10 : ℝ) ^ 100 := by positivity
  have htPos : 0 < t := htenPowPos.trans_le ht
  have hlogMono := Real.strictMonoOn_log.monotoneOn htenPowPos htPos ht
  have hlogPow : Real.log ((10 : ℝ) ^ 100) = 100 * Real.log 10 := by
    rw [Real.log_pow]
    norm_num
  rw [hlogPow] at hlogMono
  nlinarith [twenty_three_tenths_lt_log_ten]

theorem thirty_seven_le_log_rpow_two_thirds
    {t : ℝ} (ht : (10 : ℝ) ^ 100 ≤ t) :
    37 ≤ Real.log t ^ ((2 : ℝ) / 3) := by
  have hlogLower := two_hundred_thirty_le_log_of_ten_pow_hundred_le ht
  have hlogNonneg : 0 ≤ Real.log t := by linarith
  have hyNonneg : 0 ≤ Real.log t ^ ((2 : ℝ) / 3) :=
    Real.rpow_nonneg hlogNonneg _
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 37) hyNonneg
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hCube : (Real.log t ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) =
      (Real.log t) ^ (2 : ℕ) := by
    calc
      (Real.log t ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) =
          (Real.log t ^ ((2 : ℝ) / 3)) ^ (3 : ℝ) := by
            exact (Real.rpow_natCast _ 3).symm
      _ = Real.log t ^ (((2 : ℝ) / 3) * 3) := by
        exact (Real.rpow_mul hlogNonneg ((2 : ℝ) / 3) 3).symm
      _ = Real.log t ^ (2 : ℝ) := by norm_num
      _ = (Real.log t) ^ (2 : ℕ) := Real.rpow_natCast _ 2
  rw [hCube]
  nlinarith [sq_nonneg (Real.log t - 230)]

theorem ford_source_cube_root_le :
    (133.66 : ℝ) ^ ((1 : ℝ) / 3) ≤ 5.113 := by
  have hbase : 0 ≤ (133.66 : ℝ) := by norm_num
  have hroot : 0 ≤ (133.66 : ℝ) ^ ((1 : ℝ) / 3) :=
    Real.rpow_nonneg hbase _
  apply (pow_le_pow_iff_left₀ hroot (by norm_num : (0 : ℝ) ≤ 5.113)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hCube : ((133.66 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = 133.66 := by
    calc
      ((133.66 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) =
          ((133.66 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) := by
            exact (Real.rpow_natCast _ 3).symm
      _ = (133.66 : ℝ) ^ (((1 : ℝ) / 3) * 3) := by
        exact (Real.rpow_mul hbase ((1 : ℝ) / 3) 3).symm
      _ = 133.66 := by norm_num
  rw [hCube]
  norm_num

theorem fordTinyRemainder_le_one_thousandth :
    fordTinyRemainder ≤ (1 / 1000 : ℝ) := by
  unfold fordTinyRemainder
  norm_num

theorem fordLemma73_coefficient_le_76_2
    {t : ℝ} (ht : (10 : ℝ) ^ 100 ≤ t) :
    (9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3) ≤ 76.2 := by
  have hlogPow := thirty_seven_le_log_rpow_two_thirds ht
  have hlogPowPos : 0 < Real.log t ^ ((2 : ℝ) / 3) :=
    (by norm_num : (0 : ℝ) < 37).trans_le hlogPow
  have hnum :
      9.463 + 1 + fordTinyRemainder ≤ (10.464 : ℝ) := by
    linarith [fordTinyRemainder_le_one_thousandth]
  have hnumNonneg : 0 ≤ 9.463 + 1 + fordTinyRemainder := by
    have htiny : 0 ≤ fordTinyRemainder := by
      unfold fordTinyRemainder
      positivity
    positivity
  have hfraction :
      (9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) ≤ 10.464 / 37 := by
    calc
      _ ≤ 10.464 / Real.log t ^ ((2 : ℝ) / 3) := by
        exact div_le_div_of_nonneg_right hnum hlogPowPos.le
      _ ≤ 10.464 / 37 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogPow
  calc
    (9.463 + 1 + fordTinyRemainder) /
          Real.log t ^ ((2 : ℝ) / 3) +
        1.569 * 9.463 * 133.66 ^ ((1 : ℝ) / 3) ≤
      10.464 / 37 + 1.569 * 9.463 * 5.113 := by
        gcongr
        exact ford_source_cube_root_le
    _ ≤ 76.2 := by norm_num

#print axioms twenty_three_tenths_lt_log_ten
#print axioms thirty_seven_le_log_rpow_two_thirds
#print axioms ford_source_cube_root_le
#print axioms fordLemma73_coefficient_le_76_2

end

end GafniTao
