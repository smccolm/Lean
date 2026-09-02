import GafniTao.FordSmallLambdaBound

/-!
# Physical/logarithmic scale bridges for Ford's Theorem 2

Ford states the estimate using both `N <= t` and
`lambda = log t / log N`.  These lemmas derive, rather than assume, the
corresponding lower bound on `lambda` and the upper physical powers used by
the B- and A-process branches.
-/

namespace GafniTao

noncomputable section

theorem one_le_fordLambda
    {N : ℕ} {t : ℝ} (hN : 1 < N) (hNt : (N : ℝ) ≤ t) :
    1 ≤ fordLambda N t := by
  have hNpos : (0 : ℝ) < N := by positivity
  have ht : 0 < t := hNpos.trans_le hNt
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hlog := Real.strictMonoOn_log.monotoneOn hNpos ht hNt
  unfold fordLambda
  rw [le_div_iff₀ hlogN]
  simpa using hlog

theorem ford_height_le_rpow_of_lambda_le
    {N : ℕ} {t a : ℝ} (hN : 1 < N) (ht : 0 < t)
    (hlambda : fordLambda N t ≤ a) :
    t ≤ (N : ℝ) ^ a := by
  rw [← ford_rpow_lambda_eq_height hN ht]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) hlambda

theorem ford_height_le_square_of_lambda_le_two
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t)
    (hlambda : fordLambda N t ≤ 2) :
    t ≤ (N : ℝ) ^ 2 := by
  simpa only [Real.rpow_two] using
    ford_height_le_rpow_of_lambda_le hN ht hlambda

theorem ford_shifted_exponential_sum_small_lambda_physical
    {N R : ℕ} {u t : ℝ} (hN : 1024 ≤ N) (hNR : N < R)
    (hR : R ≤ 2 * N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hNt : (N : ℝ) ≤ t)
    (hlambdaUpper : fordLambda N t ≤ 19 / 10) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      130 * (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) := by
  have hNgt : 1 < N := by omega
  have ht : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < N) hNt
  have hlambdaLower := one_le_fordLambda hNgt hNt
  have htN := ford_height_le_square_of_lambda_le_two hNgt ht
    (hlambdaUpper.trans (by norm_num))
  exact ford_shifted_exponential_sum_small_lambda
    hN hNR hR hu0 hu1 hNt htN hlambdaLower hlambdaUpper

#print axioms one_le_fordLambda
#print axioms ford_height_le_square_of_lambda_le_two
#print axioms ford_shifted_exponential_sum_small_lambda_physical

end

end GafniTao
