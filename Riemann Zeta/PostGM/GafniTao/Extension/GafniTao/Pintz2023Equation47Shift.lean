import GafniTao.Pintz2023Equation45Tail

/-!
# Pintz (2023), equation (4.7): displacement to `Re s = 1/lambda`

The finite source interval is moved across a pole-free positive strip.  This
file proves the complete-line identity; the ordinate truncation and its
uniform error are kept in the next module.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

noncomputable section

theorem integrable_pintz2023BareWeightIntegrand_vertical_pos
    {lambda h c : ℝ} (hlambda : 0 < lambda) (hc : 0 < c) :
    Integrable (fun t : ℝ =>
      pintz2023BareWeightIntegrand lambda h
        ((c : ℂ) + (t : ℂ) * I)) := by
  let C : ℝ := (1 / c) * Real.exp (c ^ 2 / lambda + h * c)
  have hmajor : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)).const_mul C
  apply Integrable.mono' hmajor
  · have hline : Continuous (fun t : ℝ =>
        ((c : ℂ) + (t : ℂ) * I)) := by fun_prop
    have hnum : Continuous (fun t : ℝ =>
        pintzSourceWeightNumerator lambda h
          ((c : ℂ) + (t : ℂ) * I)) := by
      unfold pintzSourceWeightNumerator
      fun_prop
    have hden : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * I) ≠ 0 := by
      intro t hzero
      have hre := congrArg Complex.re hzero
      norm_num at hre
      linarith
    exact (hnum.div hline hden).aestronglyMeasurable
  · filter_upwards [] with t
    simpa [C, mul_assoc] using
      (norm_pintz2023BareWeightIntegrand_vertical_le_div
        (h := h) (c := c) (t := t) hlambda hc)

theorem norm_pintz2023BareWeightIntegrand_horizontal_left_le
    {lambda h a x R : ℝ} (hlambda : 0 < lambda)
    (ha : 0 < a) (hxLower : a ≤ x) (hxUpper : x ≤ 3) :
    ‖pintz2023BareWeightIntegrand lambda h
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (1 / a) * Real.exp (9 / lambda + |h| * 3) *
        Real.exp (-(1 / lambda) * R ^ 2) := by
  have hxPos : 0 < x := ha.trans_le hxLower
  have hx0 : 0 ≤ x := hxPos.le
  have hxSq : x ^ 2 ≤ 9 := by nlinarith
  have hxDiv : x ^ 2 / lambda ≤ 9 / lambda :=
    (div_le_div_iff_of_pos_right hlambda).mpr hxSq
  have hhx : h * x ≤ |h| * 3 := by
    calc
      h * x ≤ |h| * x :=
        mul_le_mul_of_nonneg_right (le_abs_self h) hx0
      _ ≤ |h| * 3 :=
        mul_le_mul_of_nonneg_left hxUpper (abs_nonneg h)
  have hinv : 1 / x ≤ 1 / a :=
    one_div_le_one_div_of_le ha hxLower
  have hexp : Real.exp (x ^ 2 / lambda + h * x) ≤
      Real.exp (9 / lambda + |h| * 3) :=
    Real.exp_le_exp.mpr (add_le_add hxDiv hhx)
  have hvertical := norm_pintz2023BareWeightIntegrand_vertical_le_div
    (h := h) (c := x) (t := R) hlambda hxPos
  calc
    ‖pintz2023BareWeightIntegrand lambda h
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (1 / x) * (Real.exp (x ^ 2 / lambda + h * x) *
        Real.exp (-(1 / lambda) * R ^ 2)) := hvertical
    _ ≤ (1 / a) * (Real.exp (9 / lambda + |h| * 3) *
        Real.exp (-(1 / lambda) * R ^ 2)) := by
      gcongr
    _ = _ := by ring

private theorem norm_pintz2023Left_normalization_le_one :
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I]
  norm_num
  rw [abs_of_pos Real.pi_pos]
  have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
    (inv_le_one₀ Real.pi_pos).2 hpi
  calc
    Real.pi⁻¹ * (1 / 2 : ℝ) ≤ 1 * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hpiInv (by norm_num)
    _ ≤ 1 := by norm_num

theorem norm_pintz2023BareWeight_HIntegral'_left_le
    {lambda h a R : ℝ} (hlambda : 0 < lambda)
    (ha : 0 < a) (ha3 : a ≤ 3) :
    ‖HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 R‖ ≤
      (3 - a) * ((1 / a) * Real.exp (9 / lambda + |h| * 3) *
        Real.exp (-(1 / lambda) * R ^ 2)) := by
  have hbase :
      ‖HIntegral (pintz2023BareWeightIntegrand lambda h) a 3 R‖ ≤
        ((1 / a) * Real.exp (9 / lambda + |h| * 3) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |3 - a| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc a (3 : ℝ) := by
      rw [← Set.uIcc_of_le ha3]
      exact Set.uIoc_subset_uIcc hx
    exact norm_pintz2023BareWeightIntegrand_horizontal_left_le
      hlambda ha hx'.1 hx'.2
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (pintz2023BareWeightIntegrand lambda h) a 3 R‖ ≤
      1 * (((1 / a) * Real.exp (9 / lambda + |h| * 3) *
        Real.exp (-(1 / lambda) * R ^ 2)) * |3 - a|) :=
      mul_le_mul norm_pintz2023Left_normalization_le_one hbase
        (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [abs_of_nonneg (sub_nonneg.mpr ha3)]
      ring

theorem tendsto_pintz2023BareWeight_HIntegral'_left_zero
    {lambda h a : ℝ} (hlambda : 0 < lambda)
    (ha : 0 < a) (ha3 : a ≤ 3) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 R)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R =>
      norm_pintz2023BareWeight_HIntegral'_left_le hlambda ha ha3)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambda
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((3 - a) * ((1 / a) * Real.exp (9 / lambda + |h| * 3)))

theorem tendsto_pintz2023BareWeight_HIntegral'_left_neg_zero
    {lambda h a : ℝ} (hlambda : 0 < lambda)
    (ha : 0 < a) (ha3 : a ≤ 3) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 (-R))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R => by
      simpa only [neg_sq] using
        norm_pintz2023BareWeight_HIntegral'_left_le
          (R := -R) (h := h) hlambda ha ha3)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambda
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((3 - a) * ((1 / a) * Real.exp (9 / lambda + |h| * 3)))

theorem differentiableOn_pintz2023BareWeightIntegrand_positive
    {lambda h : ℝ} :
    DifferentiableOn ℂ (pintz2023BareWeightIntegrand lambda h)
      {s : ℂ | 0 < s.re} := by
  intro s hs
  have hsZero : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  unfold pintz2023BareWeightIntegrand pintzSourceWeightNumerator
  exact (by fun_prop : DifferentiableAt ℂ
    (fun z : ℂ => Complex.exp
      (z ^ 2 / (lambda : ℂ) + (h : ℂ) * z) / z) s)
    |>.differentiableWithinAt

theorem pintz2023BareWeight_rectangle_left_vanishes
    {lambda h a R : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) (hR : 0 ≤ R) :
    RectangleIntegral (pintz2023BareWeightIntegrand lambda h)
      ((a : ℂ) + (-R : ℂ) * I)
      ((3 : ℂ) + (R : ℂ) * I) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle
    differentiableOn_pintz2023BareWeightIntegrand_positive
  intro s hs
  have hRe :
      (((a : ℂ) + (-R : ℂ) * I).re) ≤
        (((3 : ℂ) + (R : ℂ) * I).re) := by simpa using ha3
  have hIm :
      (((a : ℂ) + (-R : ℂ) * I).im) ≤
        (((3 : ℂ) + (R : ℂ) * I).im) := by
    norm_num [Complex.mul_im]
    linarith
  have hmem := (mem_Rect hRe hIm s).mp hs
  change 0 < s.re
  have : a ≤ s.re := by simpa using hmem.1
  linarith

theorem tendsto_pintz2023BareWeight_VIntegral'_positive
    {lambda h c : ℝ} (hlambda : 0 < lambda) (hc : 0 < c) :
    Tendsto (fun R : ℝ =>
      VIntegral' (pintz2023BareWeightIntegrand lambda h) c (-R) R)
      atTop (nhds (pintz2023BareWeight lambda h c)) := by
  have hint := intervalIntegral_tendsto_integral
    (integrable_pintz2023BareWeightIntegrand_vertical_pos
      (h := h) hlambda hc)
    tendsto_neg_atTop_atBot tendsto_id
  unfold VIntegral' VIntegral pintz2023BareWeight
    VerticalIntegral' VerticalIntegral
  have hint' : Tendsto (fun R : ℝ =>
      ∫ y in (-R)..R,
        pintz2023BareWeightIntegrand lambda h
          ((c : ℂ) + (y : ℂ) * I))
      atTop
      (nhds (∫ t : ℝ,
        pintz2023BareWeightIntegrand lambda h
          ((c : ℂ) + (t : ℂ) * I))) := by
    simpa only [id_eq, mul_comm] using hint
  exact Tendsto.smul tendsto_const_nhds
    (Tendsto.smul tendsto_const_nhds hint')

theorem pintz2023BareWeight_finite_vertical_shift_left
    {lambda h a R : ℝ} (ha : 0 < a) (ha3 : a ≤ 3) (hR : 0 ≤ R) :
    VIntegral' (pintz2023BareWeightIntegrand lambda h) 3 (-R) R =
      VIntegral' (pintz2023BareWeightIntegrand lambda h) a (-R) R -
        HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 (-R) +
        HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 R := by
  have hrect := pintz2023BareWeight_rectangle_left_vanishes
    (lambda := lambda) (h := h) ha ha3 hR
  have hraw :
      VIntegral (pintz2023BareWeightIntegrand lambda h) 3 (-R) R =
        VIntegral (pintz2023BareWeightIntegrand lambda h) a (-R) R -
          HIntegral (pintz2023BareWeightIntegrand lambda h) a 3 (-R) +
          HIntegral (pintz2023BareWeightIntegrand lambda h) a 3 R := by
    unfold RectangleIntegral at hrect
    norm_num [Complex.mul_re, Complex.mul_im] at hrect
    linear_combination hrect
  unfold VIntegral' HIntegral'
  rw [← smul_sub, ← smul_add]
  exact congrArg ((1 / (2 * Real.pi * I) : ℂ) • ·) hraw

theorem pintz2023BareWeight_complete_vertical_shift_left
    {lambda h a : ℝ} (hlambda : 0 < lambda)
    (ha : 0 < a) (ha3 : a ≤ 3) :
    pintz2023BareWeight lambda h 3 = pintz2023BareWeight lambda h a := by
  have hright := tendsto_pintz2023BareWeight_VIntegral'_positive
    (h := h) (c := 3) hlambda (by norm_num)
  have hleft := tendsto_pintz2023BareWeight_VIntegral'_positive
    (h := h) (c := a) hlambda ha
  have htop := tendsto_pintz2023BareWeight_HIntegral'_left_zero
    (h := h) hlambda ha ha3
  have hbottom := tendsto_pintz2023BareWeight_HIntegral'_left_neg_zero
    (h := h) hlambda ha ha3
  have hrhs : Tendsto (fun R : ℝ =>
      VIntegral' (pintz2023BareWeightIntegrand lambda h) a (-R) R -
        HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 (-R) +
        HIntegral' (pintz2023BareWeightIntegrand lambda h) a 3 R)
      atTop (nhds (pintz2023BareWeight lambda h a)) := by
    simpa using (hleft.sub hbottom).add htop
  exact tendsto_nhds_unique hright (hrhs.congr'
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      exact (pintz2023BareWeight_finite_vertical_shift_left
        (lambda := lambda) (h := h) ha ha3 hR).symm))

/-- Complete-line equation-(4.7) shift for each positive integer. -/
theorem pintz2023GaussianWeight_eq_smallLine
    {lambda : ℝ} {n : ℕ} (hlambda : 1 ≤ lambda) (hn : 0 < n) :
    pintz2023GaussianWeight lambda n =
      pintz2023BareWeight lambda (lambda - Real.log n) (1 / lambda) := by
  rw [pintz2023GaussianWeight_eq_bare hn]
  exact pintz2023BareWeight_complete_vertical_shift_left
    (by linarith) (by positivity) (by
      have hInv : 1 / lambda ≤ 1 / 1 :=
        one_div_le_one_div_of_le (by norm_num) hlambda
      norm_num at hInv ⊢
      linarith)

#print axioms pintz2023BareWeight_complete_vertical_shift_left
#print axioms pintz2023GaussianWeight_eq_smallLine

end

end GafniTao
