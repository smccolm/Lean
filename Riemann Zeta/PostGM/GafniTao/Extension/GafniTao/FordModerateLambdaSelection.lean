import GafniTao.FordModerateExponential
import GafniTao.FordLargeLambdaSelection

/-!
# Selecting and uniformizing the moderate Ford degree

For `49 <= lambda <= 700`, `ceil(10 lambda / 7)` lies in the complete
Lemma-5.1 band and between `40` and `1000`.  Since only finitely many degrees
occur, summing their nonnegative coefficients gives one uniform constant.
-/

namespace GafniTao

noncomputable section

def fordModerateMomentCoefficientChosen (k : ℕ) : ℝ :=
  if hk : 4 ≤ k then Classical.choose (ford_moderate_moment_bound hk) else 1

theorem fordModerateMomentCoefficientChosen_bound
    {k : ℕ} (hk : 4 ≤ k) :
    FordVinogradovMomentBound (fordModerateMomentDegree k) k
      (fordModerateMomentCoefficientChosen k) (fordModerateMomentDelta k) := by
  simp only [fordModerateMomentCoefficientChosen, dif_pos hk]
  exact Classical.choose_spec (ford_moderate_moment_bound hk)

theorem fordModerateMomentCoefficientChosen_nonneg (k : ℕ) :
    0 ≤ fordModerateMomentCoefficientChosen k := by
  by_cases hk : 4 ≤ k
  · exact zero_le_one.trans
      (fordModerateMomentCoefficientChosen_bound hk).one_le_coefficient
  · simp [fordModerateMomentCoefficientChosen, hk]

def fordModerateDegreeConstant (k : ℕ) : ℝ :=
  3 + 2 * (fordModerateCoreCoefficient k
    (fordModerateMomentCoefficientChosen k)) ^
      (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ))

theorem fordModerateDegreeConstant_nonneg (k : ℕ) :
    0 ≤ fordModerateDegreeConstant k := by
  unfold fordModerateDegreeConstant
  exact add_nonneg (by norm_num) (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (fordModerateCoreCoefficient_nonneg k
      (fordModerateMomentCoefficientChosen k)) _))

def fordModerateAbsoluteConstant : ℝ :=
  ∑ k ∈ Finset.range 1001, fordModerateDegreeConstant k

theorem fordModerateDegreeConstant_le_absolute
    {k : ℕ} (hk : k ≤ 1000) :
    fordModerateDegreeConstant k ≤ fordModerateAbsoluteConstant := by
  unfold fordModerateAbsoluteConstant
  exact Finset.single_le_sum
    (fun i _ => fordModerateDegreeConstant_nonneg i)
    (Finset.mem_range.mpr (by omega))

theorem fordModerateAbsoluteConstant_nonneg :
    0 ≤ fordModerateAbsoluteConstant := by
  unfold fordModerateAbsoluteConstant
  exact Finset.sum_nonneg fun k _ => fordModerateDegreeConstant_nonneg k

theorem fordDegreeFromLambda_moderate_band
    {lambda : ℝ} (hlower : 49 ≤ lambda) :
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

theorem fordDegreeFromLambda_moderate_lower
    {lambda : ℝ} (hlower : 49 ≤ lambda) :
    40 ≤ fordDegreeFromLambda lambda := by
  have hx : (70 : ℝ) ≤ (10 / 7 : ℝ) * lambda := by linarith
  have hceil : (70 : ℝ) ≤ (fordDegreeFromLambda lambda : ℝ) :=
    hx.trans (by unfold fordDegreeFromLambda; exact Nat.le_ceil _)
  exact_mod_cast (show (40 : ℕ) ≤ 70 by omega).trans
    (by exact_mod_cast hceil : 70 ≤ fordDegreeFromLambda lambda)

theorem fordDegreeFromLambda_moderate_upper
    {lambda : ℝ} (hupper : lambda ≤ 700) :
    fordDegreeFromLambda lambda ≤ 1000 := by
  have hx : (10 / 7 : ℝ) * lambda ≤ 1000 := by linarith
  unfold fordDegreeFromLambda
  exact Nat.ceil_le.mpr hx

theorem fordDegreeFromLambda_moderate_le_three_halves
    {lambda : ℝ} (hlower : 49 ≤ lambda) :
    (fordDegreeFromLambda lambda : ℝ) ≤ (3 / 2 : ℝ) * lambda := by
  have hlambda0 : 0 ≤ lambda := by linarith
  have hx0 : (0 : ℝ) ≤ (10 / 7 : ℝ) * lambda := by positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  unfold fordDegreeFromLambda
  nlinarith

theorem ford_moderate_degree_decay_compare
    {lambda : ℝ} (hlower : 49 ≤ lambda) :
    1 - 1 / ((665600 : ℝ) * (fordDegreeFromLambda lambda : ℝ) ^ 2) ≤
      1 - 1 / ((3000000 : ℝ) * lambda ^ 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hkPos : (0 : ℝ) < fordDegreeFromLambda lambda := by
    have hk := fordDegreeFromLambda_moderate_lower hlower
    positivity
  have hkTop := fordDegreeFromLambda_moderate_le_three_halves hlower
  have hsquare : (fordDegreeFromLambda lambda : ℝ) ^ 2 ≤
      (9 / 4 : ℝ) * lambda ^ 2 := by nlinarith
  have hden : (665600 : ℝ) * (fordDegreeFromLambda lambda : ℝ) ^ 2 ≤
      3000000 * lambda ^ 2 := by nlinarith [sq_nonneg lambda]
  have hleftPos : (0 : ℝ) <
      665600 * (fordDegreeFromLambda lambda : ℝ) ^ 2 := by positivity
  have hinv : 1 / ((3000000 : ℝ) * lambda ^ 2) ≤
      1 / ((665600 : ℝ) * (fordDegreeFromLambda lambda : ℝ) ^ 2) :=
    one_div_le_one_div_of_le hleftPos hden
  linarith

theorem ford_shifted_exponential_sum_moderate_lambda
    {N R : ℕ} {u t : ℝ}
    (hN : 1024 ≤ N) (hR : R ≤ 2 * N)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t)
    (hlambda : 49 ≤ fordLambda N t)
    (hlambdaTop : fordLambda N t ≤ 700) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordModerateAbsoluteConstant * (N : ℝ) ^
        (1 - 1 / ((3000000 : ℝ) * fordLambda N t ^ 2)) := by
  let lambda := fordLambda N t
  let k := fordDegreeFromLambda lambda
  have hk : 40 ≤ k := by
    simpa [k, lambda] using fordDegreeFromLambda_moderate_lower hlambda
  have hkTop : k ≤ 1000 := by
    simpa [k, lambda] using fordDegreeFromLambda_moderate_upper hlambdaTop
  obtain ⟨hbandLower, hbandUpper⟩ := fordDegreeFromLambda_moderate_band hlambda
  let C := fordModerateMomentCoefficientChosen k
  have hmoment : FordVinogradovMomentBound (fordModerateMomentDegree k) k C
      (fordModerateMomentDelta k) := by
    exact fordModerateMomentCoefficientChosen_bound (by omega : 4 ≤ k)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact fordModerateMomentCoefficientChosen_nonneg k
  have hsource := ford_exponential_lemma_5_1_moderate hk hN hR hu huOne ht
    hC hmoment (by simpa [k, lambda] using hbandLower)
      (by simpa [k, lambda] using hbandUpper)
  let ek : ℝ := 1 - 1 / ((665600 : ℝ) * (k : ℝ) ^ 2)
  let e : ℝ := 1 - 1 / ((3000000 : ℝ) * lambda ^ 2)
  have hcombine :
      (N : ℝ) * (N : ℝ) ^
          (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) =
        (N : ℝ) ^ ek := by
    dsimp [ek]
    calc
      (N : ℝ) * (N : ℝ) ^
          (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) =
        (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^
          (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) +
          -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
      _ = _ := by congr 1
  have hboundaryExponent : (3 / 10 : ℝ) ≤ ek := by
    have hkR : (40 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : (2 : ℝ) ≤ 665600 * (k : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((k : ℝ) - 40)]
    have hinv : 1 / (665600 * (k : ℝ) ^ 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hden
    dsimp [ek]
    linarith
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hboundary := Real.rpow_le_rpow_of_exponent_le hNreal hboundaryExponent
  have hdegree : fordModerateDegreeConstant k ≤ fordModerateAbsoluteConstant :=
    fordModerateDegreeConstant_le_absolute hkTop
  have hexponent : ek ≤ e := by
    dsimp [ek, e, k, lambda]
    exact ford_moderate_degree_decay_compare hlambda
  have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
  apply hsource.trans
  have hA0 : 0 ≤ (fordModerateCoreCoefficient k C) ^
      (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) :=
    Real.rpow_nonneg (fordModerateCoreCoefficient_nonneg k C) _
  calc
    3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (N : ℝ) * (fordModerateCoreCoefficient k C) ^
            (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
            (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) =
        3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (fordModerateCoreCoefficient k C) ^
            (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
            ((N : ℝ) *
              (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)))) := by ring
    _ = 3 * (N : ℝ) ^ (3 / 10 : ℝ) +
          2 * (fordModerateCoreCoefficient k C) ^
            (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
            (N : ℝ) ^ ek := by rw [hcombine]
    _ ≤ fordModerateDegreeConstant k * (N : ℝ) ^ ek := by
      unfold fordModerateDegreeConstant
      dsimp [C]
      calc
        3 * (N : ℝ) ^ (3 / 10 : ℝ) +
            2 * (fordModerateCoreCoefficient k
              (fordModerateMomentCoefficientChosen k)) ^
                (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
              (N : ℝ) ^ ek ≤
          3 * (N : ℝ) ^ ek +
            2 * (fordModerateCoreCoefficient k
              (fordModerateMomentCoefficientChosen k)) ^
                (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
              (N : ℝ) ^ ek := by
            exact add_le_add (mul_le_mul_of_nonneg_left hboundary (by norm_num)) le_rfl
        _ = (3 + 2 * (fordModerateCoreCoefficient k
              (fordModerateMomentCoefficientChosen k)) ^
                (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ))) *
              (N : ℝ) ^ ek := by ring
    _ ≤ fordModerateAbsoluteConstant * (N : ℝ) ^ ek := by gcongr
    _ ≤ fordModerateAbsoluteConstant * (N : ℝ) ^ e := by
      exact mul_le_mul_of_nonneg_left hpow fordModerateAbsoluteConstant_nonneg
    _ = _ := by rfl

#print axioms fordModerateMomentCoefficientChosen_bound
#print axioms fordModerateDegreeConstant_le_absolute
#print axioms fordDegreeFromLambda_moderate_band
#print axioms ford_shifted_exponential_sum_moderate_lambda

end

end GafniTao
