import GafniTao.FordLemma51AllLargeLambda

/-!
# Selecting Ford's degree from the logarithmic scale
-/

namespace GafniTao

noncomputable section

def fordDegreeFromLambda (lambda : ℝ) : ℕ :=
  ⌈(10 / 7 : ℝ) * lambda⌉₊

theorem fordDegreeFromLambda_ge_thousand
    {lambda : ℝ} (hlambda : 700 ≤ lambda) :
    1000 ≤ fordDegreeFromLambda lambda := by
  have hx0 : (0 : ℝ) ≤ (10 / 7 : ℝ) * lambda := by positivity
  have hx : (1000 : ℝ) ≤ (10 / 7 : ℝ) * lambda := by linarith
  have hceil : (1000 : ℝ) ≤ (fordDegreeFromLambda lambda : ℝ) := by
    exact hx.trans (by
      unfold fordDegreeFromLambda
      exact Nat.le_ceil _)
  exact_mod_cast hceil

theorem fordDegreeFromLambda_band
    {lambda : ℝ} (hlambda : 700 ≤ lambda) :
    (69 / 100 : ℝ) * fordDegreeFromLambda lambda ≤ lambda ∧
      lambda ≤ (7 / 10 : ℝ) * fordDegreeFromLambda lambda := by
  let x : ℝ := (10 / 7 : ℝ) * lambda
  let k : ℕ := fordDegreeFromLambda lambda
  have hlambda0 : 0 ≤ lambda := by linarith
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have htop : (k : ℝ) < x + 1 := by
    dsimp [k, fordDegreeFromLambda]
    exact Nat.ceil_lt_add_one hx0
  have hbottom : x ≤ (k : ℝ) := by
    dsimp [k, fordDegreeFromLambda, x]
    exact Nat.le_ceil _
  constructor
  · dsimp [k, x] at htop ⊢
    nlinarith
  · dsimp [k, x] at hbottom ⊢
    nlinarith

theorem fordDegreeFromLambda_le_three_halves
    {lambda : ℝ} (hlambda : 700 ≤ lambda) :
    (fordDegreeFromLambda lambda : ℝ) ≤ (3 / 2 : ℝ) * lambda := by
  have hlambda0 : 0 ≤ lambda := by linarith
  have hx0 : (0 : ℝ) ≤ (10 / 7 : ℝ) * lambda := by positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  unfold fordDegreeFromLambda
  nlinarith

theorem ford_large_degree_decay_compare
    {lambda : ℝ} (hlambda : 700 ≤ lambda) :
    1 - 1 / ((1091200 : ℝ) * (fordDegreeFromLambda lambda : ℝ) ^ 2) ≤
      1 - 1 / ((3000000 : ℝ) * lambda ^ 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hk := fordDegreeFromLambda_ge_thousand hlambda
  have hkPos : (0 : ℝ) < fordDegreeFromLambda lambda := by positivity
  have hkTop := fordDegreeFromLambda_le_three_halves hlambda
  have hsquare : (fordDegreeFromLambda lambda : ℝ) ^ 2 ≤
      (9 / 4 : ℝ) * lambda ^ 2 := by nlinarith
  have hden : (1091200 : ℝ) * (fordDegreeFromLambda lambda : ℝ) ^ 2 ≤
      3000000 * lambda ^ 2 := by
    nlinarith [sq_nonneg lambda]
  have hleftPos : (0 : ℝ) <
      1091200 * (fordDegreeFromLambda lambda : ℝ) ^ 2 := by positivity
  have hrightPos : (0 : ℝ) < 3000000 * lambda ^ 2 := by positivity
  have hinv : 1 / ((3000000 : ℝ) * lambda ^ 2) ≤
      1 / ((1091200 : ℝ) * (fordDegreeFromLambda lambda : ℝ) ^ 2) := by
    exact one_div_le_one_div_of_le hleftPos hden
  linarith

/-- The complete large-`lambda` output of the literal Lemma 5.1 route. -/
theorem ford_shifted_exponential_sum_large_lambda
    {N R : ℕ} {u t : ℝ}
    (hN : 1024 ≤ N) (hR : R ≤ 2 * N)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlambda : 700 ≤ fordLambda N t) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordLemma51AbsoluteConstant * (N : ℝ) ^
        (1 - 1 / ((3000000 : ℝ) * fordLambda N t ^ 2)) := by
  let lambda := fordLambda N t
  let k := fordDegreeFromLambda lambda
  have hk : 1000 ≤ k := by
    simpa [k, lambda] using fordDegreeFromLambda_ge_thousand hlambda
  obtain ⟨hlower, hupper⟩ := fordDegreeFromLambda_band hlambda
  have hsource := ford_exponential_lemma_5_1_all_large_degrees
    hk hN hR hu huOne ht (by simpa [k, lambda] using hlower)
      (by simpa [k, lambda] using hupper)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hexponent := ford_large_degree_decay_compare hlambda
  exact hsource.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hNreal
      (by simpa [k, lambda] using hexponent))
    (by
      unfold fordLemma51AbsoluteConstant fordUniversalRootCoefficient
        fordAbsoluteCoefficientConstant
      positivity))

#print axioms fordDegreeFromLambda_band
#print axioms ford_shifted_exponential_sum_large_lambda

end

end GafniTao
