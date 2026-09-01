import GafniTao.FordNumericalIntegralGlobal

/-!
# Ford's certified cubic-exponential integral bound

This file restores the peak factor removed in `fordNormalizedRatio` and
combines the complete-range numerical certificate with the unimodal
sum--integral comparison used in Ford's Lemma 7.3.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

theorem fordNormalizedCubicExp_eq_peak_mul_ratio (y u : ℝ) :
    fordNormalizedCubicExp y u =
      Real.exp (2 * y ^ 3) * fordNormalizedRatio y u := by
  unfold fordNormalizedRatio
  rw [← mul_assoc, ← Real.exp_add]
  norm_num

theorem integral_fordNormalizedCubicExp_eq_peak_mul_ratio (y : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedCubicExp y u) =
      Real.exp (2 * y ^ 3) *
        ∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u := by
  simp_rw [fordNormalizedCubicExp_eq_peak_mul_ratio]
  rw [MeasureTheory.integral_const_mul]

theorem integral_fordNormalizedCubicExp_le_source_constant
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedCubicExp y u) ≤
      Real.exp (2 * y ^ 3) * (108754 / 100000 : ℝ) := by
  rw [integral_fordNormalizedCubicExp_eq_peak_mul_ratio]
  exact mul_le_mul_of_nonneg_left
    (integral_fordNormalizedRatio_le_source_constant_global hy)
    (Real.exp_pos _).le

/-- The certified peak-plus-integral estimate in the exact variables used by
Ford's dyadic logarithmic sum. -/
theorem fordCubicExpSum_le_certified
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (r : ℕ) :
    (∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j)) ≤
      Real.exp (2 * fordCubicY D sigma t ^ 3) *
        (1 + fordCubicScale D t * (108754 / 100000 : ℝ)) := by
  have hy : 0 ≤ fordCubicY D sigma t := by
    unfold fordCubicY
    positivity
  have hbase := fordCubicExpSum_le_normalized hsigma hD ht r
  have hintegral := integral_fordNormalizedCubicExp_le_source_constant hy
  have hscale : 0 ≤ fordCubicScale D t := (fordCubicScale_pos hD ht).le
  calc
    (∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j)) ≤
        Real.exp (2 * fordCubicY D sigma t ^ 3) +
          fordCubicScale D t *
            ∫ u in Set.Ioi (0 : ℝ),
              fordNormalizedCubicExp (fordCubicY D sigma t) u := hbase
    _ ≤ Real.exp (2 * fordCubicY D sigma t ^ 3) +
          fordCubicScale D t *
            (Real.exp (2 * fordCubicY D sigma t ^ 3) *
              (108754 / 100000 : ℝ)) := by
      gcongr
    _ = Real.exp (2 * fordCubicY D sigma t ^ 3) *
          (1 + fordCubicScale D t * (108754 / 100000 : ℝ)) := by ring

#print axioms integral_fordNormalizedCubicExp_le_source_constant
#print axioms fordCubicExpSum_le_certified

end

end GafniTao
