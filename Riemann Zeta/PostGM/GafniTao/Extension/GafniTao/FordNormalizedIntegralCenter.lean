import GafniTao.FordSourceScale

/-!
# Centered form of Ford's normalized cubic integral

The numerical inequality in Ford's Lemma 7.3 concerns the normalized integral
after division by its peak.  This file records the exact two one-sided cubic
profiles and their monotonicity.  These are the analytic inputs for a rigorous
interval enclosure of Ford's very tight numerical constant.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

def fordNormalizedRatio (y u : ℝ) : ℝ :=
  Real.exp (-2 * y ^ 3) * fordNormalizedCubicExp y u

def fordCenteredPositive (y v : ℝ) : ℝ :=
  Real.exp (-(v ^ 2 * (3 * y + v)))

def fordCenteredNegative (y v : ℝ) : ℝ :=
  Real.exp (-(v ^ 2 * (3 * y - v)))

theorem fordNormalizedRatio_eq_exp (y u : ℝ) :
    fordNormalizedRatio y u =
      Real.exp (3 * y ^ 2 * u - u ^ 3 - 2 * y ^ 3) := by
  unfold fordNormalizedRatio fordNormalizedCubicExp
  rw [← Real.exp_add]
  congr 1
  ring

theorem fordNormalizedRatio_add_center (y v : ℝ) :
    fordNormalizedRatio y (y + v) = fordCenteredPositive y v := by
  rw [fordNormalizedRatio_eq_exp]
  unfold fordCenteredPositive
  congr 1
  ring

theorem fordNormalizedRatio_sub_center (y v : ℝ) :
    fordNormalizedRatio y (y - v) = fordCenteredNegative y v := by
  rw [fordNormalizedRatio_eq_exp]
  unfold fordCenteredNegative
  congr 1
  ring

theorem fordCenteredPositive_exponent_antitone
    {y v w : ℝ} (hy : 0 ≤ y) (hv : 0 ≤ v) (hvw : v ≤ w) :
    -(w ^ 2 * (3 * y + w)) ≤ -(v ^ 2 * (3 * y + v)) := by
  have hw : 0 ≤ w := hv.trans hvw
  have hfactor :
      w ^ 2 * (3 * y + w) - v ^ 2 * (3 * y + v) =
        (w - v) * (w ^ 2 + w * v + v ^ 2 + 3 * y * (w + v)) := by
    ring
  have hleft : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hright :
      0 ≤ w ^ 2 + w * v + v ^ 2 + 3 * y * (w + v) := by
    positivity
  nlinarith [mul_nonneg hleft hright]

theorem fordCenteredPositive_antitoneOn (y : ℝ) (hy : 0 ≤ y) :
    AntitoneOn (fordCenteredPositive y) (Set.Ici 0) := by
  intro v hv w hw hvw
  unfold fordCenteredPositive
  exact Real.exp_le_exp.mpr
    (fordCenteredPositive_exponent_antitone hy hv hvw)

theorem fordCenteredNegative_exponent_antitone
    {y v w : ℝ} (hv : 0 ≤ v)
    (hvw : v ≤ w) (hwy : w ≤ y) :
    -(w ^ 2 * (3 * y - w)) ≤ -(v ^ 2 * (3 * y - v)) := by
  have hw : 0 ≤ w := hv.trans hvw
  have hfactor :
      w ^ 2 * (3 * y - w) - v ^ 2 * (3 * y - v) =
        (w - v) * (3 * y * (w + v) - (w ^ 2 + w * v + v ^ 2)) := by
    ring
  have hleft : 0 ≤ w - v := sub_nonneg.mpr hvw
  have hwyMul : 3 * w * (w + v) ≤ 3 * y * (w + v) := by
    gcongr
  have hbase :
      0 ≤ 3 * w * (w + v) - (w ^ 2 + w * v + v ^ 2) := by
    nlinarith [sq_nonneg (w - v), mul_nonneg hw hv]
  have hright :
      0 ≤ 3 * y * (w + v) - (w ^ 2 + w * v + v ^ 2) := by
    linarith
  nlinarith [mul_nonneg hleft hright]

theorem fordCenteredNegative_antitoneOn (y : ℝ) :
    AntitoneOn (fordCenteredNegative y) (Set.Icc 0 y) := by
  intro v hv w hw hvw
  unfold fordCenteredNegative
  exact Real.exp_le_exp.mpr
    (fordCenteredNegative_exponent_antitone hv.1 hvw hw.2)

theorem fordCenteredPositive_antitone_y
    {y z v : ℝ} (hyz : y ≤ z) :
    fordCenteredPositive z v ≤ fordCenteredPositive y v := by
  unfold fordCenteredPositive
  apply Real.exp_le_exp.mpr
  have hmul : 3 * v ^ 2 * y ≤ 3 * v ^ 2 * z :=
    mul_le_mul_of_nonneg_left hyz (by positivity)
  nlinarith

theorem fordCenteredNegative_antitone_y
    {y z v : ℝ} (hyz : y ≤ z) :
    fordCenteredNegative z v ≤ fordCenteredNegative y v := by
  unfold fordCenteredNegative
  apply Real.exp_le_exp.mpr
  have hmul : 3 * v ^ 2 * y ≤ 3 * v ^ 2 * z :=
    mul_le_mul_of_nonneg_left hyz (by positivity)
  nlinarith

theorem fordCenteredPositive_le_cubicTail
    {y v : ℝ} (hy : 0 ≤ y) :
    fordCenteredPositive y v ≤ Real.exp (-v ^ 3) := by
  unfold fordCenteredPositive
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hy (sq_nonneg v)]

/-- Translation to the critical point, with the exact shifted half-line. -/
theorem integral_fordNormalizedRatio_shift (y : ℝ) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) =
      ∫ v in Set.Ioi (-y), fordCenteredPositive y v := by
  calc
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) =
        ∫ v : ℝ,
          (Set.Ioi (0 : ℝ)).indicator (fordNormalizedRatio y) (v + y) := by
      rw [MeasureTheory.integral_add_right_eq_self,
        MeasureTheory.integral_indicator measurableSet_Ioi]
    _ = ∫ v in Set.Ioi (-y), fordCenteredPositive y v := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v
      have hmem : v + y ∈ Set.Ioi (0 : ℝ) ↔ v ∈ Set.Ioi (-y) := by
        simp only [Set.mem_Ioi]
        constructor <;> intro h <;> linarith
      simp only [Set.indicator_apply]
      by_cases hv : v ∈ Set.Ioi (-y)
      · rw [if_pos (hmem.mpr hv), if_pos hv]
        simpa [add_comm] using fordNormalizedRatio_add_center y v
      · rw [if_neg (not_congr hmem |>.mpr hv), if_neg hv]

theorem fordCenteredPositive_exponent_le_neg
    {y v : ℝ} (hy : 0 ≤ y) (hv : 1 ≤ v) :
    -(v ^ 2 * (3 * y + v)) ≤ -v := by
  have hv0 : 0 ≤ v := by linarith
  have hvCube : v ≤ v ^ 3 := by nlinarith [sq_nonneg (v - 1)]
  have hyTerm : 0 ≤ 3 * y * v ^ 2 := by positivity
  nlinarith

theorem integrableOn_fordCenteredPositive_Ioi
    {y : ℝ} (hy : 0 ≤ y) :
    IntegrableOn (fordCenteredPositive y) (Set.Ioi (-y)) := by
  have hstart : -y ≤ (1 : ℝ) := by linarith
  have hcont : Continuous (fordCenteredPositive y) := by
    unfold fordCenteredPositive
    fun_prop
  have hcompact :
      IntegrableOn (fordCenteredPositive y) (Set.Ioc (-y) 1) := by
    exact hcont.continuousOn.integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have htail : IntegrableOn (fordCenteredPositive y) (Set.Ioi 1) := by
    apply (integrableOn_exp_neg_Ioi 1).mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      unfold fordCenteredPositive
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (fordCenteredPositive_exponent_le_neg hy hv.le)
  have hunion := hcompact.union htail
  rw [Set.Ioc_union_Ioi_eq_Ioi hstart] at hunion
  exact hunion

theorem intervalIntegral_fordCenteredPositive_neg_eq
    (y : ℝ) :
    (∫ v in -y..0, fordCenteredPositive y v) =
      ∫ v in 0..y, fordCenteredNegative y v := by
  have hpoint : ∀ v : ℝ,
      fordCenteredNegative y (-v) = fordCenteredPositive y v := by
    intro v
    unfold fordCenteredNegative fordCenteredPositive
    congr 1
    ring
  calc
    (∫ v in -y..0, fordCenteredPositive y v) =
        ∫ v in -y..0, fordCenteredNegative y (-v) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ v in 0..y, fordCenteredNegative y v := by
      rw [intervalIntegral.integral_comp_neg]
      simp

/-- Ford's normalized integral is exactly the sum of the two centered
one-sided profiles. -/
theorem integral_fordNormalizedRatio_eq_centered
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ u in Set.Ioi (0 : ℝ), fordNormalizedRatio y u) =
      (∫ v in 0..y, fordCenteredNegative y v) +
        ∫ v in Set.Ioi (0 : ℝ), fordCenteredPositive y v := by
  rw [integral_fordNormalizedRatio_shift]
  have hint := integrableOn_fordCenteredPositive_Ioi hy
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (f := fordCenteredPositive y) (a := -y) (b := 0)
    hint (hint.mono_set (Set.Ioi_subset_Ioi (neg_nonpos.mpr hy)))
  rw [intervalIntegral_fordCenteredPositive_neg_eq] at hsplit
  exact hsplit.symm

#print axioms fordNormalizedRatio_add_center
#print axioms fordNormalizedRatio_sub_center
#print axioms fordCenteredPositive_antitoneOn
#print axioms fordCenteredNegative_antitoneOn
#print axioms fordCenteredPositive_antitone_y
#print axioms fordCenteredNegative_antitone_y
#print axioms integral_fordNormalizedRatio_shift
#print axioms integrableOn_fordCenteredPositive_Ioi
#print axioms integral_fordNormalizedRatio_eq_centered

end

end GafniTao
