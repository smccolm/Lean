import GafniTao.FordLemma63DirectRange
import GafniTao.FordMediumLambda
import GafniTao.FordLambdaScale

/-!
# A complete qualitative Ford exponential-sum estimate

Gafni--Tao use only the qualitative Vinogradov--Korobov consequence of
Ford's argument.  This file assembles the six proved logarithmic-scale
ranges and handles the finitely many small integer endpoints.  It does not
identify its coefficient with Ford's optimized decimal constant.
-/

namespace GafniTao

noncomputable section

def fordQualitativeCoefficient : ℝ :=
  1024 + 130 + 90 + fordDirectCoefficient + fordCor64AbsoluteCoefficient +
    fordModerateAbsoluteConstant + fordLemma51AbsoluteConstant

theorem fordLemma51AbsoluteConstant_nonneg :
    0 ≤ fordLemma51AbsoluteConstant := by
  unfold fordLemma51AbsoluteConstant fordUniversalRootCoefficient
    fordAbsoluteCoefficientConstant
  positivity

theorem fordQualitativeCoefficient_nonneg :
    0 ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hdirect := fordDirectCoefficient_nonneg
  have hcor := fordCor64AbsoluteCoefficient_nonneg
  have hmoderate := fordModerateAbsoluteConstant_nonneg
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith

theorem fordQualitativeCoefficient_ge_1024 :
    (1024 : ℝ) ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hdirect := fordDirectCoefficient_nonneg
  have hcor := fordCor64AbsoluteCoefficient_nonneg
  have hmoderate := fordModerateAbsoluteConstant_nonneg
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith

theorem fordQualitativeCoefficient_ge_small :
    (130 : ℝ) ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hdirect := fordDirectCoefficient_nonneg
  have hcor := fordCor64AbsoluteCoefficient_nonneg
  have hmoderate := fordModerateAbsoluteConstant_nonneg
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith

theorem fordQualitativeCoefficient_ge_medium :
    (90 : ℝ) ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hdirect := fordDirectCoefficient_nonneg
  have hcor := fordCor64AbsoluteCoefficient_nonneg
  have hmoderate := fordModerateAbsoluteConstant_nonneg
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith

theorem fordQualitativeCoefficient_ge_direct :
    fordDirectCoefficient ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hcor := fordCor64AbsoluteCoefficient_nonneg
  have hmoderate := fordModerateAbsoluteConstant_nonneg
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith [fordDirectCoefficient_nonneg]

theorem fordQualitativeCoefficient_ge_cor64 :
    fordCor64AbsoluteCoefficient ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hmoderate := fordModerateAbsoluteConstant_nonneg
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith [fordDirectCoefficient_nonneg, fordCor64AbsoluteCoefficient_nonneg]

theorem fordQualitativeCoefficient_ge_moderate :
    fordModerateAbsoluteConstant ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  have hlarge := fordLemma51AbsoluteConstant_nonneg
  linarith [fordDirectCoefficient_nonneg, fordCor64AbsoluteCoefficient_nonneg,
    fordModerateAbsoluteConstant_nonneg]

theorem fordQualitativeCoefficient_ge_large :
    fordLemma51AbsoluteConstant ≤ fordQualitativeCoefficient := by
  unfold fordQualitativeCoefficient
  linarith [fordDirectCoefficient_nonneg, fordCor64AbsoluteCoefficient_nonneg,
    fordModerateAbsoluteConstant_nonneg, fordLemma51AbsoluteConstant_nonneg]

theorem ford_qualitative_exponent_mono
    {lambda D : ℝ} (hlambda : 1 ≤ lambda) (hD : 0 < D)
    (hDtop : D ≤ 3000000) :
    1 - 1 / (D * lambda ^ 2) ≤
      1 - 1 / (3000000 * lambda ^ 2) := by
  have hlambdaPos : 0 < lambda := zero_lt_one.trans_le hlambda
  have hleft : 0 < D * lambda ^ 2 := by positivity
  have hden : D * lambda ^ 2 ≤ 3000000 * lambda ^ 2 := by gcongr
  have hinv : 1 / (3000000 * lambda ^ 2) ≤ 1 / (D * lambda ^ 2) :=
    one_div_le_one_div_of_le hleft hden
  linarith

theorem ford_shifted_exponential_sum_qualitative_large_N
    {N R : ℕ} {u t : ℝ}
    (hN : 1024 ≤ N) (hNt : (N : ℝ) ≤ t)
    (hu : 0 < u) (huOne : u ≤ 1) (hRlower : N < R) (hR : R ≤ 2 * N) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordQualitativeCoefficient * (N : ℝ) ^
        (1 - 1 / (3000000 * fordLambda N t ^ 2)) := by
  have hNgt : 1 < N := by omega
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ht : 0 < t := (by positivity : (0 : ℝ) < N).trans_le hNt
  have hlambda : 1 ≤ fordLambda N t := one_le_fordLambda hNgt hNt
  by_cases h19 : fordLambda N t ≤ 19 / 10
  · have hsource := ford_shifted_exponential_sum_small_lambda_physical
      hN hRlower hR hu.le huOne hNt h19
    exact hsource.trans (mul_le_mul_of_nonneg_right
      fordQualitativeCoefficient_ge_small (Real.rpow_nonneg (by positivity) _))
  · have h19lower : 19 / 10 ≤ fordLambda N t := le_of_not_ge h19
    by_cases h26 : fordLambda N t ≤ 13 / 5
    · have hsource := ford_shifted_exponential_sum_medium_lambda
        hN hRlower hR hu.le huOne hNt h19lower h26
      exact hsource.trans (mul_le_mul_of_nonneg_right
        fordQualitativeCoefficient_ge_medium (Real.rpow_nonneg (by positivity) _))
    · have h26lower : 13 / 5 ≤ fordLambda N t := le_of_not_ge h26
      by_cases h4 : fordLambda N t ≤ 4
      · have hsource := ford_shifted_exponential_sum_direct_range
          (by omega) hRlower hR hu huOne ht h26lower h4
        have hexp := ford_qualitative_exponent_mono hlambda
          (by norm_num : (0 : ℝ) < 1000) (by norm_num : (1000 : ℝ) ≤ 3000000)
        have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexp
        exact hsource.trans ((mul_le_mul_of_nonneg_left hpow
          fordDirectCoefficient_nonneg).trans
            (mul_le_mul_of_nonneg_right fordQualitativeCoefficient_ge_direct
              (Real.rpow_nonneg (by positivity) _)))
      · have h4lower : 4 ≤ fordLambda N t := le_of_not_ge h4
        by_cases h49 : fordLambda N t ≤ 49
        · have hsource := ford_shifted_exponential_sum_cor64_range
            (by omega) hRlower hR hu huOne ht h4lower h49
          have hexp := ford_qualitative_exponent_mono hlambda
            (by norm_num : (0 : ℝ) < 100) (by norm_num : (100 : ℝ) ≤ 3000000)
          have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexp
          exact hsource.trans ((mul_le_mul_of_nonneg_left hpow
            fordCor64AbsoluteCoefficient_nonneg).trans
              (mul_le_mul_of_nonneg_right fordQualitativeCoefficient_ge_cor64
                (Real.rpow_nonneg (by positivity) _)))
        · have h49lower : 49 ≤ fordLambda N t := le_of_not_ge h49
          by_cases h700 : fordLambda N t ≤ 700
          · have hsource := ford_shifted_exponential_sum_moderate_lambda
              hN hR hu huOne ht h49lower h700
            exact hsource.trans (mul_le_mul_of_nonneg_right
              fordQualitativeCoefficient_ge_moderate
                (Real.rpow_nonneg (by positivity) _))
          · have h700lower : 700 ≤ fordLambda N t := le_of_not_ge h700
            have hsource := ford_shifted_exponential_sum_large_lambda
              hN hR hu huOne ht h700lower
            exact hsource.trans (mul_le_mul_of_nonneg_right
              fordQualitativeCoefficient_ge_large
                (Real.rpow_nonneg (by positivity) _))

theorem ford_exponential_sum_qualitative :
    FordExponentialSumEstimate fordQualitativeCoefficient 3000000 := by
  intro N R u t hNpos hNt hu huOne hRlower hR
  by_cases hlarge : 1024 ≤ N
  · exact ford_shifted_exponential_sum_qualitative_large_N
      hlarge hNt hu huOne hRlower hR
  · have hNnat : 1 ≤ N := hNpos
    have hnorm := norm_fordShiftedExponentialSum_le_N hR u t
    have hNtop : N ≤ 1024 := by omega
    have hNtopR : (N : ℝ) ≤ 1024 := by exact_mod_cast hNtop
    by_cases hNone : N = 1
    · subst N
      norm_num at hnorm
      have hnormC : ‖fordShiftedExponentialSum 1 R u t‖ ≤
          fordQualitativeCoefficient := by
        exact hnorm.trans ((by norm_num : (1 : ℝ) ≤ 1024).trans
          fordQualitativeCoefficient_ge_1024)
      simpa only [Nat.cast_one, Real.one_rpow, mul_one] using hnormC
    · have hNgt : 1 < N := lt_of_le_of_ne hNnat (Ne.symm hNone)
      have hlambda : 1 ≤ fordLambda N t := one_le_fordLambda hNgt hNt
      have hden : (1 : ℝ) ≤ 3000000 * fordLambda N t ^ 2 := by
        have hsquare : (1 : ℝ) ≤ fordLambda N t ^ 2 := by nlinarith
        nlinarith
      have hinv : 1 / (3000000 * fordLambda N t ^ 2) ≤ (1 : ℝ) :=
        (div_le_one (by positivity)).2 hden
      have hexp : 0 ≤ 1 - 1 / (3000000 * fordLambda N t ^ 2) := by linarith
      have hpow : (1 : ℝ) ≤ (N : ℝ) ^
          (1 - 1 / (3000000 * fordLambda N t ^ 2)) :=
        Real.one_le_rpow (by exact_mod_cast hNnat) hexp
      calc
        ‖fordShiftedExponentialSum N R u t‖ ≤ (N : ℝ) := hnorm
        _ ≤ 1024 := hNtopR
        _ ≤ fordQualitativeCoefficient := fordQualitativeCoefficient_ge_1024
        _ ≤ fordQualitativeCoefficient * (N : ℝ) ^
            (1 - 1 / (3000000 * fordLambda N t ^ 2)) := by
          nlinarith [fordQualitativeCoefficient_nonneg]

#print axioms ford_qualitative_exponent_mono
#print axioms ford_shifted_exponential_sum_qualitative_large_N
#print axioms ford_exponential_sum_qualitative

end

end GafniTao
