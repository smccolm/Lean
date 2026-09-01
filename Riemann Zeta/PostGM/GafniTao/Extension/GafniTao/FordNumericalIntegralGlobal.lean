import GafniTao.FordNumericalIntegralCertificate
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Ford's normalized integral: the complete parameter range

The exact Bernstein certificate controls `0 ≤ y ≤ 11 / 10`.  Ford's
normalized parameter is not bounded above, so this file treats the remaining
half-line by two elementary Gaussian majorants.  Together the two arguments
prove the numerical inequality used in Lemma 7.3 for every `y ≥ 0`.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

theorem fordCenteredNegative_le_gaussian
    {y v : ℝ} (hvy : v ≤ y) :
    fordCenteredNegative y v ≤ Real.exp (-(2 * y) * v ^ 2) := by
  unfold fordCenteredNegative
  apply Real.exp_le_exp.mpr
  have : 2 * y ≤ 3 * y - v := by linarith
  nlinarith [sq_nonneg v]

theorem fordCenteredPositive_le_gaussian
    {y v : ℝ} (hv0 : 0 ≤ v) :
    fordCenteredPositive y v ≤ Real.exp (-(3 * y) * v ^ 2) := by
  unfold fordCenteredPositive
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hv0 (sq_nonneg v)]

theorem integral_fordCenteredNegative_le_gaussian
    {y : ℝ} (hy : 0 < y) :
    (∫ v in 0..y, fordCenteredNegative y v) ≤
      ∫ v in Set.Ioi (0 : ℝ), Real.exp (-(2 * y) * v ^ 2) := by
  have hactual : IntervalIntegrable (fordCenteredNegative y) volume 0 y := by
    exact (show Continuous (fordCenteredNegative y) by
      unfold fordCenteredNegative
      fun_prop).intervalIntegrable _ _
  have hgauss : IntegrableOn (fun v : ℝ => Real.exp (-(2 * y) * v ^ 2))
      (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < 2 * y)).integrableOn
  have hgaussInterval : IntervalIntegrable
      (fun v : ℝ => Real.exp (-(2 * y) * v ^ 2)) volume 0 y :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < 2 * y)).intervalIntegrable
  calc
    (∫ v in 0..y, fordCenteredNegative y v) ≤
        ∫ v in 0..y, Real.exp (-(2 * y) * v ^ 2) := by
      apply intervalIntegral.integral_mono_on hy.le hactual hgaussInterval
      intro v hv
      exact fordCenteredNegative_le_gaussian hv.2
    _ = ∫ v in Set.Ioc (0 : ℝ) y,
          Real.exp (-(2 * y) * v ^ 2) := by
      rw [intervalIntegral.integral_of_le hy.le]
    _ ≤ ∫ v in Set.Ioi (0 : ℝ),
          Real.exp (-(2 * y) * v ^ 2) := by
      apply setIntegral_mono_set hgauss
      · filter_upwards with v
        positivity
      · exact ae_of_all _ fun _ hv => Set.Ioc_subset_Ioi_self hv

theorem integral_fordCenteredPositive_le_gaussian
    {y : ℝ} (hy : 0 < y) :
    (∫ v in Set.Ioi (0 : ℝ), fordCenteredPositive y v) ≤
      ∫ v in Set.Ioi (0 : ℝ), Real.exp (-(3 * y) * v ^ 2) := by
  have hactual : IntegrableOn (fordCenteredPositive y) (Set.Ioi 0) :=
    (integrableOn_fordCenteredPositive_Ioi hy.le).mono_set
      (Set.Ioi_subset_Ioi (neg_nonpos.mpr hy.le))
  have hgauss : IntegrableOn (fun v : ℝ => Real.exp (-(3 * y) * v ^ 2))
      (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < 3 * y)).integrableOn
  apply setIntegral_mono_on hactual hgauss measurableSet_Ioi
  intro v hv
  exact fordCenteredPositive_le_gaussian hv.le

theorem integral_fordNormalizedRatio_le_gaussians
    {y : ℝ} (hy : 0 < y) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) ≤
      Real.sqrt (Real.pi / (2 * y)) / 2 +
        Real.sqrt (Real.pi / (3 * y)) / 2 := by
  rw [integral_fordNormalizedRatio_eq_centered hy.le]
  calc
    (∫ v in 0..y, fordCenteredNegative y v) +
          ∫ v in Set.Ioi (0 : ℝ), fordCenteredPositive y v ≤
        (∫ v in Set.Ioi (0 : ℝ), Real.exp (-(2 * y) * v ^ 2)) +
          ∫ v in Set.Ioi (0 : ℝ), Real.exp (-(3 * y) * v ^ 2) := by
      exact add_le_add
        (integral_fordCenteredNegative_le_gaussian hy)
        (integral_fordCenteredPositive_le_gaussian hy)
    _ = Real.sqrt (Real.pi / (2 * y)) / 2 +
          Real.sqrt (Real.pi / (3 * y)) / 2 := by
      rw [integral_gaussian_Ioi, integral_gaussian_Ioi]

theorem sqrt_pi_div_two_y_le
    {y : ℝ} (hy : 11 / 10 ≤ y) :
    Real.sqrt (Real.pi / (2 * y)) / 2 ≤ 299 / 500 := by
  have hy0 : 0 < y := by linarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hfrac : Real.pi / (2 * y) ≤ (299 / 250 : ℝ) ^ 2 := by
    have hden : 0 < 2 * y := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hsqrt : Real.sqrt (Real.pi / (2 * y)) ≤ 299 / 250 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · exact hfrac
  linarith

theorem sqrt_pi_div_three_y_le
    {y : ℝ} (hy : 11 / 10 ≤ y) :
    Real.sqrt (Real.pi / (3 * y)) / 2 ≤ 61 / 125 := by
  have hy0 : 0 < y := by linarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hfrac : Real.pi / (3 * y) ≤ (122 / 125 : ℝ) ^ 2 := by
    have hden : 0 < 3 * y := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hsqrt : Real.sqrt (Real.pi / (3 * y)) ≤ 122 / 125 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · exact hfrac
  linarith

theorem integral_fordNormalizedRatio_le_source_constant_large
    {y : ℝ} (hy : 11 / 10 ≤ y) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) ≤
      (108754 / 100000 : ℝ) := by
  have hy0 : 0 < y := by linarith
  calc
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) ≤
        Real.sqrt (Real.pi / (2 * y)) / 2 +
          Real.sqrt (Real.pi / (3 * y)) / 2 :=
      integral_fordNormalizedRatio_le_gaussians hy0
    _ ≤ 299 / 500 + 61 / 125 := by
      exact add_le_add (sqrt_pi_div_two_y_le hy)
        (sqrt_pi_div_three_y_le hy)
    _ ≤ (108754 / 100000 : ℝ) := by norm_num

/-- Ford's numerical integral inequality on its complete source range. -/
theorem integral_fordNormalizedRatio_le_source_constant_global
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) ≤
      (108754 / 100000 : ℝ) := by
  by_cases hsmall : y ≤ 11 / 10
  · exact integral_fordNormalizedRatio_le_source_constant hy hsmall
  · exact integral_fordNormalizedRatio_le_source_constant_large
      (le_of_lt (lt_of_not_ge hsmall))

#print axioms integral_fordNormalizedRatio_le_gaussians
#print axioms integral_fordNormalizedRatio_le_source_constant_large
#print axioms integral_fordNormalizedRatio_le_source_constant_global

end

end GafniTao
