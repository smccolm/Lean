import GafniTao.FordPolynomialCertificate

/-!
# A rational-polynomial majorant for Ford's normalized integral

The compact pieces use finite Taylor enclosures.  The infinite positive tail
uses the tangent line to the convex cubic phase at `v = 3/2`.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

def fordNegativePhasePolynomial : FordBiPolynomial :=
  fordBiV ^ 2 * (fordBiRat 3 * fordBiY - fordBiV)

def fordPositivePhasePolynomial : FordBiPolynomial :=
  fordBiV ^ 2 * (fordBiRat 3 * fordBiY + fordBiV)

def fordNegativeUpperPolynomial : FordBiPolynomial :=
  fordScaledTaylorPolynomial 3 6 fordNegativePhasePolynomial

def fordPositiveUpperPolynomial : FordBiPolynomial :=
  fordScaledTaylorPolynomial 11 6 fordPositivePhasePolynomial

def fordTailPhasePolynomial : FordBiPolynomial :=
  fordBiRat (27 / 4) * fordBiY + fordBiRat (27 / 8)

def fordTailUpperPolynomial : FordBiPolynomial :=
  fordScaledTaylorPolynomial 11 8 fordTailPhasePolynomial

def fordNumericalPolynomialUpper (y : ℝ) : ℝ :=
  (fordBiPrimitiveValue fordNegativeUpperPolynomial y y -
      fordBiPrimitiveValue fordNegativeUpperPolynomial y 0) +
    (fordBiPrimitiveValue fordPositiveUpperPolynomial y (3 / 2) -
      fordBiPrimitiveValue fordPositiveUpperPolynomial y 0) +
    fordBiPolynomialEval fordTailUpperPolynomial y 0 / (9 * y + 27 / 4)

@[simp] theorem fordNegativePhasePolynomial_eval (y v : ℝ) :
    fordBiPolynomialEval fordNegativePhasePolynomial y v =
      v ^ 2 * (3 * y - v) := by
  simp [fordNegativePhasePolynomial]

@[simp] theorem fordPositivePhasePolynomial_eval (y v : ℝ) :
    fordBiPolynomialEval fordPositivePhasePolynomial y v =
      v ^ 2 * (3 * y + v) := by
  simp [fordPositivePhasePolynomial]

@[simp] theorem fordTailPhasePolynomial_eval (y v : ℝ) :
    fordBiPolynomialEval fordTailPhasePolynomial y v =
      27 / 4 * y + 27 / 8 := by
  simp [fordTailPhasePolynomial]

theorem fordNegativePhase_nonneg
    {y v : ℝ} (hy : 0 ≤ y) (hvy : v ≤ y) :
    0 ≤ v ^ 2 * (3 * y - v) := by
  have : 0 ≤ 3 * y - v := by linarith
  positivity

theorem fordNegativePhase_le_three
    {y v : ℝ} (hy : y ≤ 11 / 10) (hv0 : 0 ≤ v) (hvy : v ≤ y) :
    v ^ 2 * (3 * y - v) ≤ 3 := by
  have hy0 : 0 ≤ y := hv0.trans hvy
  have hfactor : 0 ≤ (y - v) ^ 2 * (2 * y + v) := by positivity
  have hcubic : 2 * y ^ 3 ≤ 2 * (11 / 10 : ℝ) ^ 3 := by
    gcongr
  calc
    v ^ 2 * (3 * y - v) ≤ 2 * y ^ 3 := by
      nlinarith
    _ ≤ 2 * (11 / 10 : ℝ) ^ 3 := hcubic
    _ ≤ 3 := by norm_num

theorem fordPositivePhase_nonneg
    {y v : ℝ} (hy : 0 ≤ y) (hv : 0 ≤ v) :
    0 ≤ v ^ 2 * (3 * y + v) := by
  positivity

theorem fordPositivePhase_le_eleven
    {y v : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10)
    (hv0 : 0 ≤ v) (hv : v ≤ 3 / 2) :
    v ^ 2 * (3 * y + v) ≤ 11 := by
  have hsq : v ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by nlinarith [sq_nonneg (v + 3 / 2)]
  have hfactor : 3 * y + v ≤ 24 / 5 := by linarith
  calc
    v ^ 2 * (3 * y + v) ≤ (3 / 2 : ℝ) ^ 2 * (24 / 5) := by
      gcongr
    _ ≤ 11 := by norm_num

theorem fordCenteredNegative_le_polynomial
    {y v : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10)
    (hv0 : 0 ≤ v) (hv : v ≤ y) :
    fordCenteredNegative y v ≤
      fordBiPolynomialEval fordNegativeUpperPolynomial y v := by
  unfold fordCenteredNegative fordNegativeUpperPolynomial
  rw [← fordNegativePhasePolynomial_eval]
  apply real_exp_neg_le_fordScaledTaylorPolynomial (by norm_num) (by norm_num)
  · simpa only [fordNegativePhasePolynomial_eval] using
      fordNegativePhase_nonneg hy0 hv
  · simpa only [fordNegativePhasePolynomial_eval] using
      fordNegativePhase_le_three hy hv0 hv

theorem fordCenteredPositive_le_polynomial
    {y v : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10)
    (hv0 : 0 ≤ v) (hv : v ≤ 3 / 2) :
    fordCenteredPositive y v ≤
      fordBiPolynomialEval fordPositiveUpperPolynomial y v := by
  unfold fordCenteredPositive fordPositiveUpperPolynomial
  rw [← fordPositivePhasePolynomial_eval]
  apply real_exp_neg_le_fordScaledTaylorPolynomial (by norm_num) (by norm_num)
  · simpa only [fordPositivePhasePolynomial_eval] using
      fordPositivePhase_nonneg hy0 hv0
  · simpa only [fordPositivePhasePolynomial_eval] using
      fordPositivePhase_le_eleven hy0 hy hv0 hv

theorem fordPositivePhase_tangent
    {y v : ℝ} (hy : 0 ≤ y) (hv : 3 / 2 ≤ v) :
    (27 / 4 * y + 27 / 8) +
        (9 * y + 27 / 4) * (v - 3 / 2) ≤
      v ^ 2 * (3 * y + v) := by
  have hdiff : 0 ≤ v - 3 / 2 := sub_nonneg.mpr hv
  have hfactor : 0 ≤ v + 3 + 3 * y := by positivity
  nlinarith [mul_nonneg (sq_nonneg (v - 3 / 2)) hfactor]

theorem fordCenteredPositive_tail_pointwise
    {y v : ℝ} (hy : 0 ≤ y) (hv : v ∈ Set.Ioi (3 / 2 : ℝ)) :
    fordCenteredPositive y v ≤
      Real.exp (-(27 / 4 * y + 27 / 8) +
          (9 * y + 27 / 4) * (3 / 2)) *
        Real.exp (-(9 * y + 27 / 4) * v) := by
  unfold fordCenteredPositive
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have htangent := fordPositivePhase_tangent hy hv.le
  nlinarith

theorem fordCenteredPositive_tail_integral_le
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ v in Set.Ioi (3 / 2 : ℝ), fordCenteredPositive y v) ≤
      Real.exp (-(27 / 4 * y + 27 / 8)) / (9 * y + 27 / 4) := by
  let d : ℝ := 9 * y + 27 / 4
  let c : ℝ := Real.exp (-(27 / 4 * y + 27 / 8) + d * (3 / 2))
  have hd : 0 < d := by dsimp [d]; positivity
  have hactual : IntegrableOn (fordCenteredPositive y) (Set.Ioi (3 / 2 : ℝ)) :=
    (integrableOn_fordCenteredPositive_Ioi hy).mono_set
      (Set.Ioi_subset_Ioi (by linarith : -y ≤ (3 / 2 : ℝ)))
  have henvelope : IntegrableOn (fun v : ℝ => c * Real.exp (-d * v))
      (Set.Ioi (3 / 2 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hd) (3 / 2)).const_mul c
  have hmono :
      (∫ v in Set.Ioi (3 / 2 : ℝ), fordCenteredPositive y v) ≤
        ∫ v in Set.Ioi (3 / 2 : ℝ), c * Real.exp (-d * v) := by
    apply MeasureTheory.integral_mono_ae hactual henvelope
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    simpa [c, d] using fordCenteredPositive_tail_pointwise hy hv
  calc
    (∫ v in Set.Ioi (3 / 2 : ℝ), fordCenteredPositive y v) ≤
        ∫ v in Set.Ioi (3 / 2 : ℝ), c * Real.exp (-d * v) := hmono
    _ = c * (-Real.exp (-d * (3 / 2)) / (-d)) := by
      rw [MeasureTheory.integral_const_mul,
        integral_exp_mul_Ioi (neg_neg_of_pos hd)]
    _ = Real.exp (-(27 / 4 * y + 27 / 8)) / (9 * y + 27 / 4) := by
      dsimp [c, d]
      field_simp
      rw [← Real.exp_add]
      congr 1
      ring

theorem fordTailPhase_nonneg {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ 27 / 4 * y + 27 / 8 := by positivity

theorem fordTailPhase_le_eleven {y : ℝ} (hy : y ≤ 11 / 10) :
    27 / 4 * y + 27 / 8 ≤ 11 := by linarith

theorem fordTailExp_le_polynomial
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    Real.exp (-(27 / 4 * y + 27 / 8)) ≤
      fordBiPolynomialEval fordTailUpperPolynomial y 0 := by
  unfold fordTailUpperPolynomial
  rw [← fordTailPhasePolynomial_eval]
  apply real_exp_neg_le_fordScaledTaylorPolynomial (by norm_num) (by norm_num)
  · simpa only [fordTailPhasePolynomial_eval] using fordTailPhase_nonneg hy0
  · simpa only [fordTailPhasePolynomial_eval] using fordTailPhase_le_eleven hy

theorem integral_fordNormalizedRatio_le_numericalPolynomialUpper
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 11 / 10) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) ≤
      fordNumericalPolynomialUpper y := by
  rw [integral_fordNormalizedRatio_eq_centered hy0]
  have hneg :
      (∫ v in 0..y, fordCenteredNegative y v) ≤
        ∫ v in 0..y, fordBiPolynomialEval fordNegativeUpperPolynomial y v := by
    apply intervalIntegral.integral_mono_on hy0
    · exact (show Continuous (fordCenteredNegative y) by
        unfold fordCenteredNegative
        fun_prop).intervalIntegrable _ _
    · exact (continuous_fordBiPolynomialEval fordNegativeUpperPolynomial y).intervalIntegrable _ _
    · intro v hv
      exact fordCenteredNegative_le_polynomial hy0 hy hv.1 hv.2
  have hposCompact :
      (∫ v in 0..(3 / 2), fordCenteredPositive y v) ≤
        ∫ v in 0..(3 / 2), fordBiPolynomialEval fordPositiveUpperPolynomial y v := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (show Continuous (fordCenteredPositive y) by
        unfold fordCenteredPositive
        fun_prop).intervalIntegrable _ _
    · exact (continuous_fordBiPolynomialEval fordPositiveUpperPolynomial y).intervalIntegrable _ _
    · intro v hv
      exact fordCenteredPositive_le_polynomial hy0 hy hv.1 hv.2
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (f := fordCenteredPositive y) (a := 0) (b := 3 / 2)
    ((integrableOn_fordCenteredPositive_Ioi hy0).mono_set
      (Set.Ioi_subset_Ioi (by linarith : -y ≤ (0 : ℝ))))
    ((integrableOn_fordCenteredPositive_Ioi hy0).mono_set
      (Set.Ioi_subset_Ioi (by linarith : -y ≤ (3 / 2 : ℝ))))
  rw [intervalIntegral_fordBiPolynomialEval] at hneg
  rw [intervalIntegral_fordBiPolynomialEval] at hposCompact
  rw [← hsplit]
  have hden : 0 < 9 * y + 27 / 4 := by positivity
  have htail := fordCenteredPositive_tail_integral_le hy0
  have htailPoly := div_le_div_of_nonneg_right
    (fordTailExp_le_polynomial hy0 hy) hden.le
  unfold fordNumericalPolynomialUpper
  linarith

#print axioms fordCenteredPositive_tail_integral_le
#print axioms integral_fordNormalizedRatio_le_numericalPolynomialUpper

end

end GafniTao
