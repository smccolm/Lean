import GafniTao.FordSmallLambdaB

/-!
# Ford-form estimate on the first small-lambda slice

The B-process gives square-root-in-height cancellation.  This file converts
that physical estimate to the common `N^(1-c/lambda^2)` normalization.  The
constant `3000000` is deliberately shared with the large-lambda theorem; no
claim is made that it is Ford's optimized `133.66`.
-/

namespace GafniTao

noncomputable section

theorem ford_rpow_lambda_eq_height
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t) :
    (N : ℝ) ^ fordLambda N t = t := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  rw [Real.rpow_def_of_pos hNpos]
  unfold fordLambda
  rw [show Real.log (N : ℝ) *
      (Real.log t / Real.log (N : ℝ)) = Real.log t by field_simp]
  exact Real.exp_log ht

theorem ford_sqrt_height_eq_lambda_power
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t) :
    Real.sqrt t = (N : ℝ) ^ (fordLambda N t / 2) := by
  rw [Real.sqrt_eq_rpow]
  have heq := ford_rpow_lambda_eq_height hN ht
  calc
    t ^ (1 / 2 : ℝ) =
        ((N : ℝ) ^ fordLambda N t) ^ (1 / 2 : ℝ) :=
      congrArg (fun z : ℝ => z ^ (1 / 2 : ℝ)) heq.symm
    _ =
        (N : ℝ) ^ (fordLambda N t * (1 / 2 : ℝ)) :=
      (Real.rpow_mul (by positivity : (0 : ℝ) ≤ N) _ _).symm
    _ = (N : ℝ) ^ (fordLambda N t / 2) := by ring_nf

theorem ford_small_lambda_exponent_compare
    {lambda : ℝ} (hlower : 1 ≤ lambda) (hupper : lambda ≤ 19 / 10) :
    lambda / 2 ≤ 1 - 1 / (3000000 * lambda ^ 2) := by
  have hlambda : 0 < lambda := lt_of_lt_of_le zero_lt_one hlower
  have hden : 0 < 3000000 * lambda ^ 2 := by positivity
  have hsquare : 1 ≤ lambda ^ 2 := by nlinarith
  have hdenLower : (3000000 : ℝ) ≤ 3000000 * lambda ^ 2 := by nlinarith
  have hinv : 1 / (3000000 * lambda ^ 2) ≤ (1 / 3000000 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hdenLower
  rw [le_sub_iff_add_le]
  calc
    lambda / 2 + 1 / (3000000 * lambda ^ 2) ≤
        (19 / 10 : ℝ) / 2 + 1 / 3000000 := add_le_add
          (div_le_div_of_nonneg_right hupper (by norm_num)) hinv
    _ ≤ 1 := by norm_num

theorem ford_shifted_exponential_sum_small_lambda
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2)
    (hlambdaLower : 1 ≤ fordLambda N t)
    (hlambdaUpper : fordLambda N t ≤ 19 / 10) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      130 * (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) := by
  have hNgt : 1 < N := by omega
  have ht : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < N) hNt
  have hB := ford_shifted_exponential_sum_B_process
    hN hNR hR hu0 hu1 hNt htN
  rw [ford_sqrt_height_eq_lambda_power hNgt ht] at hB
  exact hB.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ N by omega)) <|
      ford_small_lambda_exponent_compare hlambdaLower hlambdaUpper)
    (by norm_num))

#print axioms ford_rpow_lambda_eq_height
#print axioms ford_small_lambda_exponent_compare
#print axioms ford_shifted_exponential_sum_small_lambda

end

end GafniTao
