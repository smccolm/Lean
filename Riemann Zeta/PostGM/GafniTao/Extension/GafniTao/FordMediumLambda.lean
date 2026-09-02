import GafniTao.FordShiftedWeylRange

/-!
# Ford's literal shifted sum on `1.9 <= lambda <= 2.6`

This is the public consumer of the real-base A/B process.  Its hypotheses are
exactly the physical hypotheses and Ford logarithmic scale; the split at the
square height and every real-power conversion are derived in the proof.
-/

namespace GafniTao

noncomputable section

theorem ford_medium_target_exponent_lower
    {lambda : ℝ} (hlambda : 19 / 10 ≤ lambda) :
    14 / 15 ≤ 1 - 1 / (3000000 * lambda ^ 2) := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hsquare : (19 / 10 : ℝ) ^ 2 ≤ lambda ^ 2 := by nlinarith
  have hden : 0 < 3000000 * lambda ^ 2 := by positivity
  have hinv : 1 / (3000000 * lambda ^ 2) ≤ (1 / 15 : ℝ) := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

theorem ford_shifted_exponential_sum_medium_lambda
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t)
    (hlambdaLower : 19 / 10 ≤ fordLambda N t)
    (hlambdaUpper : fordLambda N t ≤ 13 / 5) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      90 * (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) := by
  have hNgt : 1 < N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ht : 0 < t := hNpos.trans_le hNt
  have hheight := ford_rpow_lambda_eq_height hNgt ht
  have hLow : (N : ℝ) ^ (19 / 10 : ℝ) ≤ t := by
    calc
      (N : ℝ) ^ (19 / 10 : ℝ) ≤
          (N : ℝ) ^ fordLambda N t :=
        Real.rpow_le_rpow_of_exponent_le hNOne hlambdaLower
      _ = t := hheight
  have hHigh : t ≤ (N : ℝ) ^ (13 / 5 : ℝ) := by
    calc
      t = (N : ℝ) ^ fordLambda N t := hheight.symm
      _ ≤ (N : ℝ) ^ (13 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNOne hlambdaUpper
  have hexp := ford_medium_target_exponent_lower hlambdaLower
  have hpow : (N : ℝ) ^ (14 / 15 : ℝ) ≤
      (N : ℝ) ^ (1 - 1 / (3000000 * fordLambda N t ^ 2)) :=
    Real.rpow_le_rpow_of_exponent_le hNOne hexp
  rcases le_total t ((N : ℝ) ^ 2) with htN | hN2t
  · have hbase := ford_shifted_weyl_below_square_power
      hN hNR hR hu0 hu1 hNt hLow htN
    have hsmall : (N : ℝ) ^ (13 / 15 : ℝ) ≤
        (N : ℝ) ^ (14 / 15 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNOne (by norm_num)
    calc
      ‖fordShiftedExponentialSum N R u t‖ ≤
          90 * (N : ℝ) ^ (13 / 15 : ℝ) := hbase
      _ ≤ 90 * (N : ℝ) ^ (14 / 15 : ℝ) := by gcongr
      _ ≤ 90 * (N : ℝ) ^
          (1 - 1 / (3000000 * fordLambda N t ^ 2)) := by gcongr
  · have hbase := ford_shifted_weyl_above_square_power
      hN hNR hR hu0 hu1 hNt hN2t hHigh
    exact hbase.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

#print axioms ford_medium_target_exponent_lower
#print axioms ford_shifted_exponential_sum_medium_lambda

end

end GafniTao
