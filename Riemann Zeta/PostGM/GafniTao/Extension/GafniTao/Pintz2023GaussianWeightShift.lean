import GafniTao.Pintz2023Equation42Split
import GafniTao.PintzWeightShift

/-!
# Pintz (2023), equation (4.4): the bare Gaussian weight

This file moves the *actual* integer-indexed Gaussian weight occurring in
the finite-mollifier expansion from `Re s = 3` to `Re s = lambda`.  The
older `pintzSourceWeight` also contains a zeta factor and therefore cannot
serve as this step.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

noncomputable section

/-- The bare integrand after writing `n⁻ˢ` as the source displacement
`h = lambda - log n`. -/
noncomputable def pintz2023BareWeightIntegrand
    (lambda h : ℝ) (s : ℂ) : ℂ :=
  pintzSourceWeightNumerator lambda h s / s

/-- The corresponding normalized complete vertical integral. -/
noncomputable def pintz2023BareWeight
    (lambda h : ℝ) (c : ℝ) : ℂ :=
  VerticalIntegral' (pintz2023BareWeightIntegrand lambda h) c

theorem pintz2023GaussianWeight_eq_bare
    {lambda : ℝ} {n : ℕ} (hn : 0 < n) :
    pintz2023GaussianWeight lambda n =
      pintz2023BareWeight lambda (lambda - Real.log n) 3 := by
  unfold pintz2023GaussianWeight pintz2023BareWeight
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  exact pintz_mobius_kernel_eq_source_kernel hn _

theorem norm_pintz2023BareWeightIntegrand_vertical_le
    {lambda h c t : ℝ} (hlambda : 0 < lambda) (hc : 1 ≤ c) :
    ‖pintz2023BareWeightIntegrand lambda h
        ((c : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp (c ^ 2 / lambda + h * c) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
  have hc0 : 0 ≤ c := by linarith
  have hden : 1 ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
    have hre := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
    norm_num at hre ⊢
    have hcNorm : c ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
      simpa [abs_of_nonneg hc0] using hre
    exact hc.trans hcNorm
  have hnum := norm_pintzSourceWeightNumerator_vertical_factored
    lambda h c t hlambda
  unfold pintz2023BareWeightIntegrand
  rw [norm_div]
  rw [show (t : ℂ) * I = I * t by simp [mul_comm]]
  rw [hnum]
  have hden' : 1 ≤ ‖(c : ℂ) + I * t‖ := by
    simpa [mul_comm] using hden
  have hdenPos : 0 < ‖(c : ℂ) + I * t‖ :=
    lt_of_lt_of_le zero_lt_one hden'
  apply (div_le_iff₀ hdenPos).2
  calc
    Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2) =
        (Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2)) * 1 := by ring
    _ ≤ (Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2)) *
        ‖(c : ℂ) + I * t‖ :=
      mul_le_mul_of_nonneg_left hden' (by positivity)

theorem integrable_pintz2023BareWeightIntegrand_vertical
    {lambda h c : ℝ} (hlambda : 0 < lambda) (hc : 1 ≤ c) :
    Integrable (fun t : ℝ =>
      pintz2023BareWeightIntegrand lambda h
        ((c : ℂ) + (t : ℂ) * I)) := by
  let C : ℝ := Real.exp (c ^ 2 / lambda + h * c)
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
    exact norm_pintz2023BareWeightIntegrand_vertical_le hlambda hc

theorem norm_pintz2023BareWeightIntegrand_horizontal_le
    {lambda h x R : ℝ} (hlambda : 3 ≤ lambda)
    (hxLower : 3 ≤ x) (hxUpper : x ≤ lambda) :
    ‖pintz2023BareWeightIntegrand lambda h
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      Real.exp (lambda + |h| * lambda) *
        Real.exp (-(1 / lambda) * R ^ 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxSq : x ^ 2 ≤ lambda ^ 2 := by nlinarith
  have hxDiv : x ^ 2 / lambda ≤ lambda := by
    calc
      x ^ 2 / lambda ≤ lambda ^ 2 / lambda :=
        (div_le_div_iff_of_pos_right hlambdaPos).mpr hxSq
      _ = lambda := by field_simp
  have hhx : h * x ≤ |h| * lambda := by
    calc
      h * x ≤ |h| * x :=
        mul_le_mul_of_nonneg_right (le_abs_self h) hx0
      _ ≤ |h| * lambda :=
        mul_le_mul_of_nonneg_left hxUpper (abs_nonneg h)
  have hexp :
      Real.exp (x ^ 2 / lambda + h * x) ≤
        Real.exp (lambda + |h| * lambda) :=
    Real.exp_le_exp.mpr (add_le_add hxDiv hhx)
  have hvertical := norm_pintz2023BareWeightIntegrand_vertical_le
    (h := h) (t := R) hlambdaPos (by linarith : 1 ≤ x)
  exact hvertical.trans
    (mul_le_mul_of_nonneg_right hexp (by positivity))

private theorem norm_pintz2023Weight_normalization_le_one :
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

theorem norm_pintz2023BareWeight_HIntegral'_le
    {lambda h R : ℝ} (hlambda : 3 ≤ lambda) :
    ‖HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda R‖ ≤
      (lambda - 3) *
        (Real.exp (lambda + |h| * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) := by
  have hbase :
      ‖HIntegral (pintz2023BareWeightIntegrand lambda h) 3 lambda R‖ ≤
        (Real.exp (lambda + |h| * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |lambda - 3| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (3 : ℝ) lambda := by
      rw [← Set.uIcc_of_le hlambda]
      exact Set.uIoc_subset_uIcc hx
    exact norm_pintz2023BareWeightIntegrand_horizontal_le
      hlambda hx'.1 hx'.2
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ‖HIntegral (pintz2023BareWeightIntegrand lambda h) 3 lambda R‖
        ≤ 1 * ((Real.exp (lambda + |h| * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |lambda - 3|) :=
      mul_le_mul norm_pintz2023Weight_normalization_le_one hbase
        (norm_nonneg _) (by positivity)
    _ = (lambda - 3) *
        (Real.exp (lambda + |h| * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlambda)]
      ring

theorem tendsto_pintz2023BareWeight_HIntegral'_zero
    {lambda h : ℝ} (hlambda : 3 ≤ lambda) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda R)
      atTop (nhds 0) := by
  have hlambdaPos : 0 < lambda := by linarith
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R =>
      norm_pintz2023BareWeight_HIntegral'_le hlambda)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambdaPos
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((lambda - 3) * Real.exp (lambda + |h| * lambda))

theorem tendsto_pintz2023BareWeight_HIntegral'_neg_zero
    {lambda h : ℝ} (hlambda : 3 ≤ lambda) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda (-R))
      atTop (nhds 0) := by
  have hlambdaPos : 0 < lambda := by linarith
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R => by
      simpa only [neg_sq] using
        norm_pintz2023BareWeight_HIntegral'_le
          (R := -R) (h := h) hlambda)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambdaPos
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((lambda - 3) * Real.exp (lambda + |h| * lambda))

theorem differentiableOn_pintz2023BareWeightIntegrand_right
    {lambda h : ℝ} :
    DifferentiableOn ℂ (pintz2023BareWeightIntegrand lambda h)
      {s : ℂ | 2 < s.re} := by
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

theorem pintz2023BareWeight_rectangle_vanishes
    {lambda h R : ℝ} (hlambda : 3 ≤ lambda) (hR : 0 ≤ R) :
    RectangleIntegral (pintz2023BareWeightIntegrand lambda h)
      ((3 : ℂ) + (-R : ℂ) * I)
      ((lambda : ℂ) + (R : ℂ) * I) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle
    differentiableOn_pintz2023BareWeightIntegrand_right
  intro s hs
  have hRe :
      (((3 : ℂ) + (-R : ℂ) * I).re) ≤
        (((lambda : ℂ) + (R : ℂ) * I).re) := by
    simpa using hlambda
  have hIm :
      (((3 : ℂ) + (-R : ℂ) * I).im) ≤
        (((lambda : ℂ) + (R : ℂ) * I).im) := by
    norm_num [Complex.mul_im]
    linarith
  have hmem := (mem_Rect hRe hIm s).mp hs
  change 2 < s.re
  have : (3 : ℝ) ≤ s.re := by simpa using hmem.1
  linarith

theorem tendsto_pintz2023BareWeight_VIntegral'_verticalIntegral'
    {lambda h c : ℝ} (hlambda : 0 < lambda) (hc : 1 ≤ c) :
    Tendsto (fun R : ℝ =>
      VIntegral' (pintz2023BareWeightIntegrand lambda h) c (-R) R)
      atTop (nhds (pintz2023BareWeight lambda h c)) := by
  have hint := intervalIntegral_tendsto_integral
    (integrable_pintz2023BareWeightIntegrand_vertical
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

theorem pintz2023BareWeight_finite_vertical_shift
    {lambda h R : ℝ} (hlambda : 3 ≤ lambda) (hR : 0 ≤ R) :
    VIntegral' (pintz2023BareWeightIntegrand lambda h) lambda (-R) R =
      VIntegral' (pintz2023BareWeightIntegrand lambda h) 3 (-R) R -
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda (-R) +
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda R := by
  have hrect := pintz2023BareWeight_rectangle_vanishes
    (h := h) hlambda hR
  have hraw :
      VIntegral (pintz2023BareWeightIntegrand lambda h) lambda (-R) R =
        VIntegral (pintz2023BareWeightIntegrand lambda h) 3 (-R) R -
          HIntegral (pintz2023BareWeightIntegrand lambda h) 3 lambda (-R) +
          HIntegral (pintz2023BareWeightIntegrand lambda h) 3 lambda R := by
    unfold RectangleIntegral at hrect
    norm_num [Complex.mul_re, Complex.mul_im] at hrect
    linear_combination hrect
  unfold VIntegral' HIntegral'
  rw [← smul_sub, ← smul_add]
  exact congrArg ((1 / (2 * Real.pi * I) : ℂ) • ·) hraw

/-- Complete residue-free displacement of the actual bare integer weight. -/
theorem pintz2023BareWeight_complete_vertical_shift
    {lambda h : ℝ} (hlambda : 3 ≤ lambda) :
    pintz2023BareWeight lambda h 3 =
      pintz2023BareWeight lambda h lambda := by
  have hlambdaPos : 0 < lambda := by linarith
  have hright := tendsto_pintz2023BareWeight_VIntegral'_verticalIntegral'
    (h := h) (c := lambda) hlambdaPos (by linarith)
  have hleft := tendsto_pintz2023BareWeight_VIntegral'_verticalIntegral'
    (h := h) (c := 3) hlambdaPos (by norm_num)
  have htop := tendsto_pintz2023BareWeight_HIntegral'_zero
    (h := h) hlambda
  have hbottom := tendsto_pintz2023BareWeight_HIntegral'_neg_zero
    (h := h) hlambda
  have hrhs : Tendsto (fun R : ℝ =>
      VIntegral' (pintz2023BareWeightIntegrand lambda h) 3 (-R) R -
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda (-R) +
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 lambda R)
      atTop (nhds (pintz2023BareWeight lambda h 3)) := by
    simpa using (hleft.sub hbottom).add htop
  exact (tendsto_nhds_unique hright (hrhs.congr'
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      exact (pintz2023BareWeight_finite_vertical_shift
        (h := h) hlambda hR).symm))).symm

/-- Explicit complete right-line estimate.  The Gaussian integral factor is
retained exactly; no asymptotic constant is hidden. -/
theorem norm_pintz2023BareWeight_le_rightLine
    {lambda h : ℝ} (hlambda : 3 ≤ lambda) :
    ‖pintz2023BareWeight lambda h 3‖ ≤
      Real.exp (lambda + h * lambda) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
  have hlambdaPos : 0 < lambda := by linarith
  rw [pintz2023BareWeight_complete_vertical_shift hlambda]
  have hint := integrable_pintz2023BareWeightIntegrand_vertical
    (h := h) (c := lambda) hlambdaPos (by linarith)
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambdaPos)
  have hupper : Integrable (fun t : ℝ =>
      Real.exp (lambda + h * lambda) *
        Real.exp (-(1 / lambda) * t ^ 2)) :=
    hgaussian.const_mul (Real.exp (lambda + h * lambda))
  have hmono :
      ∫ t : ℝ, ‖pintz2023BareWeightIntegrand lambda h
          ((lambda : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, Real.exp (lambda + h * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
    apply integral_mono hint.norm hupper
    intro t
    simpa [show lambda ^ 2 / lambda = lambda by field_simp] using
      norm_pintz2023BareWeightIntegrand_vertical_le
        (h := h) (c := lambda) (t := t) hlambdaPos (by linarith)
  have hnormIntegral :
      ‖∫ t : ℝ, pintz2023BareWeightIntegrand lambda h
          ((lambda : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, ‖pintz2023BareWeightIntegrand lambda h
          ((lambda : ℂ) + (t : ℂ) * I)‖ :=
    norm_integral_le_integral_norm _
  unfold pintz2023BareWeight VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul, norm_I]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          (1 * ‖∫ t : ℝ, pintz2023BareWeightIntegrand lambda h
            ((lambda : ℂ) + (t : ℂ) * I)‖)
        ≤ 1 * (1 * (∫ t : ℝ,
          ‖pintz2023BareWeightIntegrand lambda h
            ((lambda : ℂ) + (t : ℂ) * I)‖)) := by
      exact mul_le_mul norm_pintz2023Weight_normalization_le_one
        (mul_le_mul_of_nonneg_left hnormIntegral (by norm_num))
        (by positivity) (by positivity)
    _ ≤ ∫ t : ℝ, Real.exp (lambda + h * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
      simpa using hmono
    _ = Real.exp (lambda + h * lambda) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
      rw [integral_const_mul, integral_gaussian]

theorem norm_pintz2023GaussianWeight_le
    {lambda : ℝ} {n : ℕ} (hlambda : 3 ≤ lambda) (hn : 0 < n) :
    ‖pintz2023GaussianWeight lambda n‖ ≤
      Real.exp (lambda + (lambda - Real.log n) * lambda) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
  rw [pintz2023GaussianWeight_eq_bare hn]
  exact norm_pintz2023BareWeight_le_rightLine hlambda

/-! The source chooses the line `Re s = lambda`.  For a quantitative
`Y⁻²` estimate after an explicit divisor-power loss it is useful (and
analytically harmless) to retain a free right line `q`. -/

theorem norm_pintz2023BareWeightIntegrand_horizontal_to_le
    {lambda h q x R : ℝ} (hlambda : 0 < lambda)
    (hq : 3 ≤ q) (hxLower : 3 ≤ x) (hxUpper : x ≤ q) :
    ‖pintz2023BareWeightIntegrand lambda h
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      Real.exp (q ^ 2 / lambda + |h| * q) *
        Real.exp (-(1 / lambda) * R ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hq0 : 0 ≤ q := by linarith
  have hxSq : x ^ 2 ≤ q ^ 2 := by nlinarith
  have hxDiv : x ^ 2 / lambda ≤ q ^ 2 / lambda :=
    (div_le_div_iff_of_pos_right hlambda).mpr hxSq
  have hhx : h * x ≤ |h| * q := by
    calc
      h * x ≤ |h| * x :=
        mul_le_mul_of_nonneg_right (le_abs_self h) hx0
      _ ≤ |h| * q :=
        mul_le_mul_of_nonneg_left hxUpper (abs_nonneg h)
  have hexp :
      Real.exp (x ^ 2 / lambda + h * x) ≤
        Real.exp (q ^ 2 / lambda + |h| * q) :=
    Real.exp_le_exp.mpr (add_le_add hxDiv hhx)
  have hvertical := norm_pintz2023BareWeightIntegrand_vertical_le
    (h := h) (t := R) hlambda (by linarith : 1 ≤ x)
  exact hvertical.trans
    (mul_le_mul_of_nonneg_right hexp (by positivity))

theorem norm_pintz2023BareWeight_HIntegral'_to_le
    {lambda h q R : ℝ} (hlambda : 0 < lambda) (hq : 3 ≤ q) :
    ‖HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q R‖ ≤
      (q - 3) *
        (Real.exp (q ^ 2 / lambda + |h| * q) *
          Real.exp (-(1 / lambda) * R ^ 2)) := by
  have hbase :
      ‖HIntegral (pintz2023BareWeightIntegrand lambda h) 3 q R‖ ≤
        (Real.exp (q ^ 2 / lambda + |h| * q) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |q - 3| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (3 : ℝ) q := by
      rw [← Set.uIcc_of_le hq]
      exact Set.uIoc_subset_uIcc hx
    exact norm_pintz2023BareWeightIntegrand_horizontal_to_le
      hlambda hq hx'.1 hx'.2
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ‖HIntegral (pintz2023BareWeightIntegrand lambda h) 3 q R‖
        ≤ 1 * ((Real.exp (q ^ 2 / lambda + |h| * q) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |q - 3|) :=
      mul_le_mul norm_pintz2023Weight_normalization_le_one hbase
        (norm_nonneg _) (by positivity)
    _ = (q - 3) *
        (Real.exp (q ^ 2 / lambda + |h| * q) *
          Real.exp (-(1 / lambda) * R ^ 2)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hq)]
      ring

theorem tendsto_pintz2023BareWeight_HIntegral'_to_zero
    {lambda h q : ℝ} (hlambda : 0 < lambda) (hq : 3 ≤ q) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q R)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R =>
      norm_pintz2023BareWeight_HIntegral'_to_le hlambda hq)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambda
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((q - 3) * Real.exp (q ^ 2 / lambda + |h| * q))

theorem tendsto_pintz2023BareWeight_HIntegral'_to_neg_zero
    {lambda h q : ℝ} (hlambda : 0 < lambda) (hq : 3 ≤ q) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q (-R))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R => by
      simpa only [neg_sq] using
        norm_pintz2023BareWeight_HIntegral'_to_le
          (R := -R) (h := h) hlambda hq)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambda
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((q - 3) * Real.exp (q ^ 2 / lambda + |h| * q))

theorem pintz2023BareWeight_rectangle_to_vanishes
    {lambda h q R : ℝ} (hq : 3 ≤ q) (hR : 0 ≤ R) :
    RectangleIntegral (pintz2023BareWeightIntegrand lambda h)
      ((3 : ℂ) + (-R : ℂ) * I)
      ((q : ℂ) + (R : ℂ) * I) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle
    differentiableOn_pintz2023BareWeightIntegrand_right
  intro s hs
  have hRe :
      (((3 : ℂ) + (-R : ℂ) * I).re) ≤
        (((q : ℂ) + (R : ℂ) * I).re) := by
    simpa using hq
  have hIm :
      (((3 : ℂ) + (-R : ℂ) * I).im) ≤
        (((q : ℂ) + (R : ℂ) * I).im) := by
    norm_num [Complex.mul_im]
    linarith
  have hmem := (mem_Rect hRe hIm s).mp hs
  change 2 < s.re
  have : (3 : ℝ) ≤ s.re := by simpa using hmem.1
  linarith

theorem pintz2023BareWeight_finite_vertical_shift_to
    {lambda h q R : ℝ} (hq : 3 ≤ q) (hR : 0 ≤ R) :
    VIntegral' (pintz2023BareWeightIntegrand lambda h) q (-R) R =
      VIntegral' (pintz2023BareWeightIntegrand lambda h) 3 (-R) R -
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q (-R) +
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q R := by
  have hrect := pintz2023BareWeight_rectangle_to_vanishes
    (lambda := lambda) (h := h) hq hR
  have hraw :
      VIntegral (pintz2023BareWeightIntegrand lambda h) q (-R) R =
        VIntegral (pintz2023BareWeightIntegrand lambda h) 3 (-R) R -
          HIntegral (pintz2023BareWeightIntegrand lambda h) 3 q (-R) +
          HIntegral (pintz2023BareWeightIntegrand lambda h) 3 q R := by
    unfold RectangleIntegral at hrect
    norm_num [Complex.mul_re, Complex.mul_im] at hrect
    linear_combination hrect
  unfold VIntegral' HIntegral'
  rw [← smul_sub, ← smul_add]
  exact congrArg ((1 / (2 * Real.pi * I) : ℂ) • ·) hraw

theorem pintz2023BareWeight_complete_vertical_shift_to
    {lambda h q : ℝ} (hlambda : 0 < lambda) (hq : 3 ≤ q) :
    pintz2023BareWeight lambda h 3 = pintz2023BareWeight lambda h q := by
  have hright := tendsto_pintz2023BareWeight_VIntegral'_verticalIntegral'
    (h := h) (c := q) hlambda (by linarith)
  have hleft := tendsto_pintz2023BareWeight_VIntegral'_verticalIntegral'
    (h := h) (c := 3) hlambda (by norm_num)
  have htop := tendsto_pintz2023BareWeight_HIntegral'_to_zero
    (h := h) hlambda hq
  have hbottom := tendsto_pintz2023BareWeight_HIntegral'_to_neg_zero
    (h := h) hlambda hq
  have hrhs : Tendsto (fun R : ℝ =>
      VIntegral' (pintz2023BareWeightIntegrand lambda h) 3 (-R) R -
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q (-R) +
        HIntegral' (pintz2023BareWeightIntegrand lambda h) 3 q R)
      atTop (nhds (pintz2023BareWeight lambda h 3)) := by
    simpa using (hleft.sub hbottom).add htop
  exact (tendsto_nhds_unique hright (hrhs.congr'
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      exact (pintz2023BareWeight_finite_vertical_shift_to
        (lambda := lambda) (h := h) hq hR).symm))).symm

theorem norm_pintz2023BareWeight_le_rightLine_to
    {lambda h q : ℝ} (hlambda : 0 < lambda) (hq : 3 ≤ q) :
    ‖pintz2023BareWeight lambda h 3‖ ≤
      Real.exp (q ^ 2 / lambda + h * q) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
  rw [pintz2023BareWeight_complete_vertical_shift_to hlambda hq]
  have hint := integrable_pintz2023BareWeightIntegrand_vertical
    (h := h) (c := q) hlambda (by linarith)
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)
  have hupper : Integrable (fun t : ℝ =>
      Real.exp (q ^ 2 / lambda + h * q) *
        Real.exp (-(1 / lambda) * t ^ 2)) :=
    hgaussian.const_mul (Real.exp (q ^ 2 / lambda + h * q))
  have hmono :
      ∫ t : ℝ, ‖pintz2023BareWeightIntegrand lambda h
          ((q : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, Real.exp (q ^ 2 / lambda + h * q) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
    apply integral_mono hint.norm hupper
    intro t
    exact norm_pintz2023BareWeightIntegrand_vertical_le
      (h := h) (c := q) (t := t) hlambda (by linarith)
  have hnormIntegral :
      ‖∫ t : ℝ, pintz2023BareWeightIntegrand lambda h
          ((q : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, ‖pintz2023BareWeightIntegrand lambda h
          ((q : ℂ) + (t : ℂ) * I)‖ :=
    norm_integral_le_integral_norm _
  unfold pintz2023BareWeight VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul, norm_I]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          (1 * ‖∫ t : ℝ, pintz2023BareWeightIntegrand lambda h
            ((q : ℂ) + (t : ℂ) * I)‖)
        ≤ 1 * (1 * (∫ t : ℝ,
          ‖pintz2023BareWeightIntegrand lambda h
            ((q : ℂ) + (t : ℂ) * I)‖)) := by
      exact mul_le_mul norm_pintz2023Weight_normalization_le_one
        (mul_le_mul_of_nonneg_left hnormIntegral (by norm_num))
        (by positivity) (by positivity)
    _ ≤ ∫ t : ℝ, Real.exp (q ^ 2 / lambda + h * q) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
      simpa using hmono
    _ = Real.exp (q ^ 2 / lambda + h * q) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
      rw [integral_const_mul, integral_gaussian]

theorem pintz2023_shifted_exponential_to_eq_rpow
    {lambda q : ℝ} {n : ℕ} (hn : 0 < n) :
    Real.exp (q ^ 2 / lambda + (lambda - Real.log n) * q) =
      Real.exp (q ^ 2 / lambda + lambda * q) / (n : ℝ) ^ q := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnReal]
  simp only [div_eq_mul_inv]
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

theorem norm_pintz2023GaussianWeight_le_on_line
    {lambda q : ℝ} {n : ℕ} (hlambda : 0 < lambda)
    (hq : 3 ≤ q) (hn : 0 < n) :
    ‖pintz2023GaussianWeight lambda n‖ ≤
      (Real.exp (q ^ 2 / lambda + lambda * q) / (n : ℝ) ^ q) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
  rw [pintz2023GaussianWeight_eq_bare hn]
  have h := norm_pintz2023BareWeight_le_rightLine_to
    (h := lambda - Real.log n) hlambda hq
  rw [pintz2023_shifted_exponential_to_eq_rpow hn] at h
  exact h

/-- The sharpened line estimate retains the denominator `|q+it| ≥ q`.
This removes the spurious `sqrt lambda` loss from the tail ledger. -/
theorem norm_pintz2023BareWeightIntegrand_vertical_le_div
    {lambda h c t : ℝ} (hlambda : 0 < lambda) (hc : 0 < c) :
    ‖pintz2023BareWeightIntegrand lambda h
        ((c : ℂ) + (t : ℂ) * I)‖ ≤
      (1 / c) * (Real.exp (c ^ 2 / lambda + h * c) *
        Real.exp (-(1 / lambda) * t ^ 2)) := by
  have hcNorm : c ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
    have hre := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
    norm_num at hre ⊢
    simpa [abs_of_pos hc] using hre
  have hdenPos : 0 < ‖(c : ℂ) + (t : ℂ) * I‖ :=
    hc.trans_le hcNorm
  have hnum := norm_pintzSourceWeightNumerator_vertical_factored
    lambda h c t hlambda
  unfold pintz2023BareWeightIntegrand
  rw [norm_div]
  rw [show (t : ℂ) * I = I * t by simp [mul_comm]]
  rw [hnum]
  have hdenPos' : 0 < ‖(c : ℂ) + I * t‖ := by
    simpa [mul_comm] using hdenPos
  apply (div_le_iff₀ hdenPos').2
  calc
    Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2) =
        ((1 / c) * (Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2))) * c := by
      field_simp
    _ ≤ ((1 / c) * (Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2))) *
        ‖(c : ℂ) + I * t‖ :=
      mul_le_mul_of_nonneg_left
        (by simpa [mul_comm] using hcNorm) (by positivity)

theorem norm_pintz2023BareWeight_le_rightLine_to_div
    {lambda h q : ℝ} (hlambda : 0 < lambda) (hq : 3 ≤ q) :
    ‖pintz2023BareWeight lambda h 3‖ ≤
      (1 / q) * Real.exp (q ^ 2 / lambda + h * q) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
  rw [pintz2023BareWeight_complete_vertical_shift_to hlambda hq]
  have hint := integrable_pintz2023BareWeightIntegrand_vertical
    (h := h) (c := q) hlambda (by linarith)
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)
  let C : ℝ := (1 / q) * Real.exp (q ^ 2 / lambda + h * q)
  have hupper : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    hgaussian.const_mul C
  have hmono :
      ∫ t : ℝ, ‖pintz2023BareWeightIntegrand lambda h
          ((q : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, C * Real.exp (-(1 / lambda) * t ^ 2) := by
    apply integral_mono hint.norm hupper
    intro t
    simpa [C, mul_assoc] using
      (norm_pintz2023BareWeightIntegrand_vertical_le_div
        (h := h) (c := q) (t := t) hlambda (by linarith))
  have hnormIntegral :
      ‖∫ t : ℝ, pintz2023BareWeightIntegrand lambda h
          ((q : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t : ℝ, ‖pintz2023BareWeightIntegrand lambda h
          ((q : ℂ) + (t : ℂ) * I)‖ :=
    norm_integral_le_integral_norm _
  unfold pintz2023BareWeight VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul, norm_I]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          (1 * ‖∫ t : ℝ, pintz2023BareWeightIntegrand lambda h
            ((q : ℂ) + (t : ℂ) * I)‖)
        ≤ 1 * (1 * (∫ t : ℝ,
          ‖pintz2023BareWeightIntegrand lambda h
            ((q : ℂ) + (t : ℂ) * I)‖)) := by
      exact mul_le_mul norm_pintz2023Weight_normalization_le_one
        (mul_le_mul_of_nonneg_left hnormIntegral (by norm_num))
        (by positivity) (by positivity)
    _ ≤ ∫ t : ℝ, C * Real.exp (-(1 / lambda) * t ^ 2) := by
      simpa using hmono
    _ = (1 / q) * Real.exp (q ^ 2 / lambda + h * q) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
      rw [integral_const_mul, integral_gaussian]

theorem norm_pintz2023GaussianWeight_le_on_line_div
    {lambda q : ℝ} {n : ℕ} (hlambda : 0 < lambda)
    (hq : 3 ≤ q) (hn : 0 < n) :
    ‖pintz2023GaussianWeight lambda n‖ ≤
      (1 / q) *
        (Real.exp (q ^ 2 / lambda + lambda * q) / (n : ℝ) ^ q) *
          Real.sqrt (Real.pi / (1 / lambda)) := by
  rw [pintz2023GaussianWeight_eq_bare hn]
  have h := norm_pintz2023BareWeight_le_rightLine_to_div
    (h := lambda - Real.log n) hlambda hq
  rw [pintz2023_shifted_exponential_to_eq_rpow hn] at h
  exact h

#print axioms pintz2023GaussianWeight_eq_bare
#print axioms integrable_pintz2023BareWeightIntegrand_vertical
#print axioms norm_pintz2023BareWeightIntegrand_horizontal_le
#print axioms pintz2023BareWeight_rectangle_vanishes
#print axioms pintz2023BareWeight_complete_vertical_shift
#print axioms norm_pintz2023GaussianWeight_le
#print axioms pintz2023BareWeight_complete_vertical_shift_to
#print axioms norm_pintz2023GaussianWeight_le_on_line
#print axioms norm_pintz2023GaussianWeight_le_on_line_div

end

end GafniTao
