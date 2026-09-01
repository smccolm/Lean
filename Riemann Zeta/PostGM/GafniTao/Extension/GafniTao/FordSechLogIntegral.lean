import GafniTao.FordZetaGrowthConsumer
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# An explicit integrable envelope for Ford's weighted logarithmic integral

The source uses cancellation to obtain a sharp zero error.  For the native
detector it is also useful to have a robust absolute envelope.  The lemmas
below prove that envelope from `cosh u >= exp |u| / 2` and the standard Gamma
integrals; no convergence assertion is left as a side condition.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

theorem exp_abs_le_two_mul_cosh (u : ℝ) :
    Real.exp |u| ≤ 2 * Real.cosh u := by
  rw [Real.cosh_eq]
  ring_nf
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
    exact le_add_of_nonneg_right (Real.exp_pos (-u)).le
  · rw [abs_of_neg (lt_of_not_ge hu)]
    exact le_add_of_nonneg_left (Real.exp_pos u).le

theorem one_div_cosh_sq_le_four_mul_exp_neg_two_abs (u : ℝ) :
    1 / Real.cosh u ^ 2 ≤ 4 * Real.exp (-2 * |u|) := by
  have hcosh : 0 < Real.cosh u := Real.cosh_pos u
  have hexp : 0 < Real.exp |u| := Real.exp_pos _
  have hbase := exp_abs_le_two_mul_cosh u
  have hsq : Real.exp |u| ^ 2 ≤ (2 * Real.cosh u) ^ 2 := by
    nlinarith
  have hinv : 1 / (2 * Real.cosh u) ^ 2 ≤ 1 / Real.exp |u| ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hexp) hsq
  calc
    1 / Real.cosh u ^ 2 = 4 * (1 / (2 * Real.cosh u) ^ 2) := by
      field_simp [hcosh.ne']
      ring
    _ ≤ 4 * (1 / Real.exp |u| ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 4 * Real.exp (-2 * |u|) := by
      rw [show -2 * |u| = -(2 * |u|) by ring, Real.exp_neg,
        show 2 * |u| = |u| + |u| by ring, Real.exp_add]
      field_simp [hexp.ne']

theorem integrable_abs_add_one_mul_exp_neg_two_abs :
    Integrable (fun u : ℝ => (|u| + 1) * Real.exp (-2 * |u|)) := by
  have hzero : IntegrableOn
      (fun x : ℝ => Real.exp (-2 * x)) (Ioi 0) := by
    simpa using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (0 : ℝ)) (p := (1 : ℝ)) (b := (2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hone : IntegrableOn
      (fun x : ℝ => x * Real.exp (-2 * x)) (Ioi 0) := by
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (1 : ℝ)) (p := (1 : ℝ)) (b := (2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num))
  have hposRaw : IntegrableOn
      (fun x : ℝ => (x + 1) * Real.exp (-2 * x)) (Ioi 0) := by
    refine (hone.add hzero).congr_fun ?_ measurableSet_Ioi
    intro x _hx
    change x * Real.exp (-2 * x) + Real.exp (-2 * x) =
      (x + 1) * Real.exp (-2 * x)
    ring
  have hpos : IntegrableOn
      (fun x : ℝ => (|x| + 1) * Real.exp (-2 * |x|)) (Ioi 0) :=
    hposRaw.congr_fun (by
      intro x hx
      change (x + 1) * Real.exp (-2 * x) =
        (|x| + 1) * Real.exp (-2 * |x|)
      rw [abs_of_pos hx]) measurableSet_Ioi
  have hnegRaw := hposRaw.comp_neg
  have hnegRaw' : IntegrableOn
      (fun x : ℝ => ((-x) + 1) * Real.exp (-2 * (-x))) (Iio 0) := by
    simpa [Set.neg_Ioi] using hnegRaw
  have hneg : IntegrableOn
      (fun x : ℝ => (|x| + 1) * Real.exp (-2 * |x|)) (Iio 0) :=
    hnegRaw'.congr_fun (by
      intro x hx
      change ((-x) + 1) * Real.exp (-2 * (-x)) =
        (|x| + 1) * Real.exp (-2 * |x|)
      rw [abs_of_neg hx]) measurableSet_Iio
  have hleft : IntegrableOn
      (fun x : ℝ => (|x| + 1) * Real.exp (-2 * |x|)) (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).2 hneg
  have hall := hleft.union hpos
  rw [Iic_union_Ioi] at hall
  exact integrableOn_univ.mp hall

theorem log_abs_add_two_le_abs_add_one (u : ℝ) :
    Real.log (|u| + 2) ≤ |u| + 1 := by
  have hpos : 0 < |u| + 2 := by positivity
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- Absolute integrability of the precise logarithmic envelope used after
the affine-height reduction. -/
theorem integrable_log_abs_add_two_div_cosh_sq :
    Integrable (fun u : ℝ =>
      Real.log (|u| + 2) / Real.cosh u ^ 2) := by
  have hmajor :=
    integrable_abs_add_one_mul_exp_neg_two_abs.const_mul (4 : ℝ)
  apply hmajor.mono'
  · have hlog : Continuous (fun u : ℝ => Real.log (|u| + 2)) := by
      apply Continuous.log
      · fun_prop
      · intro u
        positivity
    exact (hlog.div (Real.continuous_cosh.pow 2)
      (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).aestronglyMeasurable
  filter_upwards [] with u
  have hlogNonneg : 0 ≤ Real.log (|u| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg u])
  have hcoshSq : 0 < Real.cosh u ^ 2 := sq_pos_of_pos (Real.cosh_pos u)
  have hsech := one_div_cosh_sq_le_four_mul_exp_neg_two_abs u
  have hlog := log_abs_add_two_le_abs_add_one u
  have hexp : 0 ≤ Real.exp (-2 * |u|) := (Real.exp_pos _).le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hlogNonneg hcoshSq.le)]
  calc
    Real.log (|u| + 2) / Real.cosh u ^ 2 =
        Real.log (|u| + 2) * (1 / Real.cosh u ^ 2) := by ring
    _ ≤ Real.log (|u| + 2) * (4 * Real.exp (-2 * |u|)) :=
      mul_le_mul_of_nonneg_left hsech hlogNonneg
    _ ≤ (|u| + 1) * (4 * Real.exp (-2 * |u|)) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = 4 * ((|u| + 1) * Real.exp (-2 * |u|)) := by ring

/-- The finite positive number measuring the fixed logarithmic loss in the
coarse Ford integral envelope. -/
noncomputable def fordSechLogMoment : ℝ :=
  ∫ u : ℝ, Real.log (|u| + 2) / Real.cosh u ^ 2

theorem fordSechLogMoment_nonneg : 0 ≤ fordSechLogMoment := by
  unfold fordSechLogMoment
  apply integral_nonneg
  intro u
  exact div_nonneg
    (Real.log_nonneg (by linarith [abs_nonneg u]))
    (sq_nonneg _)

theorem intervalIntegral_log_abs_add_two_div_cosh_sq_le
    {a b : ℝ} (hab : a ≤ b) :
    (∫ u in a..b,
      Real.log (|u| + 2) / Real.cosh u ^ 2) ≤
      fordSechLogMoment := by
  rw [intervalIntegral.integral_of_le hab]
  unfold fordSechLogMoment
  apply setIntegral_le_integral integrable_log_abs_add_two_div_cosh_sq
  filter_upwards [] with u
  exact div_nonneg
    (Real.log_nonneg (by linarith [abs_nonneg u]))
    (sq_nonneg _)

#print axioms integrable_log_abs_add_two_div_cosh_sq
#print axioms fordSechLogMoment_nonneg
#print axioms intervalIntegral_log_abs_add_two_div_cosh_sq_le

end

end GafniTao
