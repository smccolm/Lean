import GafniTao.PintzSourceWeight

/-!
# Rightward displacement of Pintz's individual weights

For `lambda ≥ 3`, Pintz moves the defining line of `w_ρ(h)` from real
part `3` to real part `lambda`.  This is the step that exposes the strong
factor `exp(lambda * h)` and makes the tail in equation (4.4) uniform.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Exact Gaussian norm on a vertical line for the source-facing numerator. -/
theorem norm_pintzSourceWeightNumerator_vertical
    (lambda h c t : ℝ) (hlambda : 0 < lambda) :
    ‖pintzSourceWeightNumerator lambda h
        ((c : ℂ) + I * t)‖ =
      Real.exp ((c ^ 2 - t ^ 2) / lambda + h * c) := by
  rw [pintzSourceWeightNumerator, Complex.norm_exp]
  congr 1
  rw [Complex.add_re, Complex.div_re]
  simp [Complex.normSq_apply, pow_two]
  field_simp [ne_of_gt hlambda]

/-- Factored form of the preceding vertical Gaussian identity. -/
theorem norm_pintzSourceWeightNumerator_vertical_factored
    (lambda h c t : ℝ) (hlambda : 0 < lambda) :
    ‖pintzSourceWeightNumerator lambda h
        ((c : ℂ) + I * t)‖ =
      Real.exp (c ^ 2 / lambda + h * c) *
        Real.exp (-(1 / lambda) * t ^ 2) := by
  rw [norm_pintzSourceWeightNumerator_vertical lambda h c t hlambda]
  rw [← Real.exp_add]
  congr 1
  field_simp [ne_of_gt hlambda]
  ring

/-- The literal integrand defining `w_ρ(h)`. -/
noncomputable def pintzSourceWeightIntegrand
    (rho : ℂ) (lambda h : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + rho) * pintzSourceWeightNumerator lambda h s / s

/-- On every line to the right of `3`, the individual-weight integrand has
an integrable Gaussian majorant independent of the ordinate of `rho`. -/
theorem norm_pintzSourceWeightIntegrand_vertical_le
    {rho : ℂ} {lambda h c t : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 0 < lambda) (hc : 3 <= c) :
    ‖pintzSourceWeightIntegrand rho lambda h
        ((c : ℂ) + (t : ℂ) * I)‖ <=
      hughesYoungZetaHalfPlaneMajorant *
        Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
  have hzeta :
      ‖riemannZeta (((c : ℂ) + (t : ℂ) * I) + rho)‖ <=
        hughesYoungZetaHalfPlaneMajorant :=
    norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant (by
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero]
      linarith)
  have hden : 1 <= ‖(c : ℂ) + (t : ℂ) * I‖ := by
    have hre := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)
    norm_num at hre ⊢
    have hc0 : 0 <= c := by linarith
    have hcNorm : c <= ‖(c : ℂ) + (t : ℂ) * I‖ := by
      simpa [abs_of_nonneg hc0] using hre
    exact (by linarith : (1 : ℝ) <= c).trans hcNorm
  have hnum := norm_pintzSourceWeightNumerator_vertical_factored
    lambda h c t hlambda
  have hnum' :
      ‖pintzSourceWeightNumerator lambda h
        ((c : ℂ) + (t : ℂ) * I)‖ =
        Real.exp (c ^ 2 / lambda + h * c) *
          Real.exp (-(1 / lambda) * t ^ 2) := by
    simpa [mul_comm] using hnum
  have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant :=
    tsum_nonneg (fun _ => norm_nonneg _)
  unfold pintzSourceWeightIntegrand
  rw [norm_div, norm_mul, hnum']
  calc
    ‖riemannZeta ((c : ℂ) + (t : ℂ) * I + rho)‖ *
          (Real.exp (c ^ 2 / lambda + h * c) *
            Real.exp (-(1 / lambda) * t ^ 2)) /
          ‖(c : ℂ) + (t : ℂ) * I‖
        <= hughesYoungZetaHalfPlaneMajorant *
          (Real.exp (c ^ 2 / lambda + h * c) *
            Real.exp (-(1 / lambda) * t ^ 2)) / 1 := by
      exact div_le_div₀
        (mul_nonneg hHnonneg (by positivity))
        (mul_le_mul_of_nonneg_right hzeta (by positivity))
        (by positivity) hden
    _ = _ := by ring

/-- Absolute integrability of the individual-weight integrand on all lines
used by the rightward displacement. -/
theorem integrable_pintzSourceWeightIntegrand_vertical
    {rho : ℂ} {lambda h c : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 0 < lambda) (hc : 3 <= c) :
    Integrable (fun t : ℝ =>
      pintzSourceWeightIntegrand rho lambda h
        ((c : ℂ) + (t : ℂ) * I)) := by
  let C : ℝ := hughesYoungZetaHalfPlaneMajorant *
    Real.exp (c ^ 2 / lambda + h * c)
  have hmajor : Integrable (fun t : ℝ =>
      C * Real.exp (-(1 / lambda) * t ^ 2)) :=
    (integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)).const_mul C
  apply Integrable.mono' hmajor
  · have hline : Continuous (fun t : ℝ =>
        ((c : ℂ) + (t : ℂ) * I)) := by fun_prop
    have hzeta : Continuous (fun t : ℝ =>
        riemannZeta (((c : ℂ) + (t : ℂ) * I) + rho)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (analyticAt_riemannZeta (by
        intro hone
        have hre := congrArg Complex.re hone
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          zero_mul, mul_zero, sub_zero, one_re] at hre
        linarith)).continuousAt.comp (hline.add continuous_const).continuousAt
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
    exact ((hzeta.mul hnum).div hline hden).aestronglyMeasurable
  · filter_upwards [] with t
    exact norm_pintzSourceWeightIntegrand_vertical_le
      hrho hlambda hc

/-- Uniform Gaussian decay on a horizontal edge of the right-shift
rectangle. -/
theorem norm_pintzSourceWeightIntegrand_horizontal_le
    {rho : ℂ} {lambda h x R : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda)
    (hxLower : 3 <= x) (hxUpper : x <= lambda) :
    ‖pintzSourceWeightIntegrand rho lambda h
        ((x : ℂ) + (R : ℂ) * I)‖ <=
      hughesYoungZetaHalfPlaneMajorant *
        Real.exp (lambda + |h| * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hx0 : 0 <= x := by linarith
  have hzeta :
      ‖riemannZeta (((x : ℂ) + (R : ℂ) * I) + rho)‖ <=
        hughesYoungZetaHalfPlaneMajorant :=
    norm_riemannZeta_le_hughesYoungZetaHalfPlaneMajorant (by
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero]
      linarith)
  have hden : 1 <= ‖(x : ℂ) + (R : ℂ) * I‖ := by
    have hre := Complex.abs_re_le_norm ((x : ℂ) + (R : ℂ) * I)
    norm_num at hre ⊢
    have hxNorm : x <= ‖(x : ℂ) + (R : ℂ) * I‖ := by
      simpa [abs_of_nonneg hx0] using hre
    exact (by linarith : (1 : ℝ) <= x).trans hxNorm
  have hxSq : x ^ 2 <= lambda ^ 2 := by nlinarith
  have hxDiv : x ^ 2 / lambda <= lambda := by
    calc
      x ^ 2 / lambda <= lambda ^ 2 / lambda :=
        (div_le_div_iff_of_pos_right hlambdaPos).mpr hxSq
      _ = lambda := by field_simp
  have hhx : h * x <= |h| * lambda := by
    calc
      h * x <= |h| * x :=
        mul_le_mul_of_nonneg_right (le_abs_self h) hx0
      _ <= |h| * lambda :=
        mul_le_mul_of_nonneg_left hxUpper (abs_nonneg h)
  have hexp :
      Real.exp (x ^ 2 / lambda + h * x) <=
        Real.exp (lambda + |h| * lambda) :=
    Real.exp_le_exp.mpr (add_le_add hxDiv hhx)
  have hnum := norm_pintzSourceWeightNumerator_vertical_factored
    lambda h x R hlambdaPos
  have hnum' :
      ‖pintzSourceWeightNumerator lambda h
          ((x : ℂ) + (R : ℂ) * I)‖ <=
        Real.exp (lambda + |h| * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2) := by
    rw [show (R : ℂ) * I = I * R by simp [mul_comm]]
    rw [hnum]
    exact mul_le_mul_of_nonneg_right hexp (by positivity)
  have hHnonneg : 0 <= hughesYoungZetaHalfPlaneMajorant :=
    tsum_nonneg (fun _ => norm_nonneg _)
  unfold pintzSourceWeightIntegrand
  rw [norm_div, norm_mul]
  calc
    ‖riemannZeta ((x : ℂ) + (R : ℂ) * I + rho)‖ *
          ‖pintzSourceWeightNumerator lambda h
            ((x : ℂ) + (R : ℂ) * I)‖ /
          ‖(x : ℂ) + (R : ℂ) * I‖
        <= hughesYoungZetaHalfPlaneMajorant *
            (Real.exp (lambda + |h| * lambda) *
              Real.exp (-(1 / lambda) * R ^ 2)) / 1 := by
      exact div_le_div₀
        (mul_nonneg hHnonneg (by positivity))
        (mul_le_mul hzeta hnum' (norm_nonneg _) hHnonneg)
        (by positivity) hden
    _ = _ := by ring

private theorem norm_pintzWeight_normalization_le_one :
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ <= 1 := by
  rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
    Complex.norm_I]
  norm_num
  rw [abs_of_pos Real.pi_pos]
  have hpi : (1 : ℝ) <= Real.pi := by nlinarith [Real.pi_gt_three]
  have hpiInv : Real.pi⁻¹ <= (1 : ℝ) :=
    (inv_le_one₀ Real.pi_pos).2 hpi
  calc
    Real.pi⁻¹ * (1 / 2 : ℝ) <= 1 * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hpiInv (by norm_num)
    _ <= 1 := by norm_num

/-- Quantitative bound for either horizontal edge of the right-shift
rectangle. -/
theorem norm_pintzSourceWeight_HIntegral'_le
    {rho : ℂ} {lambda h R : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) :
    ‖HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda R‖ <=
      (lambda - 3) *
        (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + |h| * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2)) := by
  have hbase :
      ‖HIntegral (pintzSourceWeightIntegrand rho lambda h) 3 lambda R‖ <=
        (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + |h| * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2)) * |lambda - 3| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (3 : ℝ) lambda := by
      rw [← Set.uIcc_of_le hlambda]
      exact Set.uIoc_subset_uIcc hx
    exact norm_pintzSourceWeightIntegrand_horizontal_le
      hrho hlambda hx'.1 hx'.2
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          ‖HIntegral (pintzSourceWeightIntegrand rho lambda h) 3 lambda R‖
        <= 1 * ((hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + |h| * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2)) * |lambda - 3|) :=
      mul_le_mul norm_pintzWeight_normalization_le_one hbase
        (norm_nonneg _) (by positivity)
    _ = (lambda - 3) *
        (hughesYoungZetaHalfPlaneMajorant *
          Real.exp (lambda + |h| * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hlambda)]
      ring

/-- Horizontal edges of the right-shift rectangle vanish at infinite
height. -/
theorem tendsto_pintzSourceWeight_HIntegral'_zero
    {rho : ℂ} {lambda h : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda R)
      atTop (nhds 0) := by
  have hlambdaPos : 0 < lambda := by linarith
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R =>
      norm_pintzSourceWeight_HIntegral'_le hrho hlambda)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambdaPos
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((lambda - 3) * hughesYoungZetaHalfPlaneMajorant *
      Real.exp (lambda + |h| * lambda))

/-- Holomorphy of the individual-weight integrand throughout the half-plane
containing Pintz's right-shift rectangles. -/
theorem differentiableOn_pintzSourceWeightIntegrand_right
    {rho : ℂ} {lambda h : ℝ} (hrho : 1 / 2 <= rho.re) :
    DifferentiableOn ℂ (pintzSourceWeightIntegrand rho lambda h)
      {s : ℂ | 2 < s.re} := by
  intro s hs
  have hsZero : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  have hsPole : s + rho ≠ 1 := by
    intro hpole
    have hre := congrArg Complex.re hpole
    simp only [add_re, one_re] at hre
    change 2 < s.re at hs
    linarith
  unfold pintzSourceWeightIntegrand pintzSourceWeightNumerator
  exact (((differentiableAt_riemannZeta hsPole).comp s (by fun_prop)).mul
    (by fun_prop)).div differentiableAt_id hsZero |>.differentiableWithinAt

/-- The finite right-shift rectangle encloses no pole. -/
theorem pintzSourceWeight_rectangle_vanishes
    {rho : ℂ} {lambda h R : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) (hR : 0 <= R) :
    RectangleIntegral (pintzSourceWeightIntegrand rho lambda h)
      ((3 : ℂ) + (-R : ℂ) * I)
      ((lambda : ℂ) + (R : ℂ) * I) = 0 := by
  apply HolomorphicOn.vanishesOnRectangle
    (differentiableOn_pintzSourceWeightIntegrand_right hrho)
  intro s hs
  have hRe :
      (((3 : ℂ) + (-R : ℂ) * I).re) <=
        (((lambda : ℂ) + (R : ℂ) * I).re) := by
    simpa using hlambda
  have hIm :
      (((3 : ℂ) + (-R : ℂ) * I).im) <=
        (((lambda : ℂ) + (R : ℂ) * I).im) := by
    norm_num [Complex.mul_im]
    linarith
  have hmem := (mem_Rect hRe hIm s).mp hs
  change 2 < s.re
  have : (3 : ℝ) <= s.re := by simpa using hmem.1
  linarith

/-- Symmetric truncations of any of the displaced vertical lines converge
to the corresponding complete normalized vertical integral. -/
theorem tendsto_pintzSourceWeight_VIntegral'_verticalIntegral'
    {rho : ℂ} {lambda h c : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 0 < lambda) (hc : 3 <= c) :
    Tendsto (fun R : ℝ =>
      VIntegral' (pintzSourceWeightIntegrand rho lambda h) c (-R) R)
      atTop
      (nhds (VerticalIntegral'
        (pintzSourceWeightIntegrand rho lambda h) c)) := by
  have hint := intervalIntegral_tendsto_integral
    (integrable_pintzSourceWeightIntegrand_vertical
      (h := h) hrho hlambda hc)
    tendsto_neg_atTop_atBot tendsto_id
  unfold VIntegral' VIntegral VerticalIntegral' VerticalIntegral
  have hint' : Tendsto (fun R : ℝ =>
      ∫ y in (-R)..R,
        pintzSourceWeightIntegrand rho lambda h
          ((c : ℂ) + (y : ℂ) * I))
      atTop
      (nhds (∫ t : ℝ,
        pintzSourceWeightIntegrand rho lambda h
          ((c : ℂ) + (t : ℂ) * I))) := by
    simpa only [id_eq, mul_comm] using hint
  exact Tendsto.smul tendsto_const_nhds
    (Tendsto.smul tendsto_const_nhds hint')

/-- Exact finite-height displacement identity, with both horizontal edges
still visible. -/
theorem pintzSourceWeight_finite_vertical_shift
    {rho : ℂ} {lambda h R : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) (hR : 0 <= R) :
    VIntegral' (pintzSourceWeightIntegrand rho lambda h) lambda (-R) R =
      VIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 (-R) R -
        HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda (-R) +
        HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda R := by
  have hrect := pintzSourceWeight_rectangle_vanishes
    (rho := rho) (h := h) hrho hlambda hR
  have hraw :
      VIntegral (pintzSourceWeightIntegrand rho lambda h) lambda (-R) R =
        VIntegral (pintzSourceWeightIntegrand rho lambda h) 3 (-R) R -
          HIntegral (pintzSourceWeightIntegrand rho lambda h) 3 lambda (-R) +
          HIntegral (pintzSourceWeightIntegrand rho lambda h) 3 lambda R := by
    unfold RectangleIntegral at hrect
    norm_num [Complex.mul_re, Complex.mul_im] at hrect
    linear_combination hrect
  unfold VIntegral' HIntegral'
  rw [← smul_sub, ← smul_add]
  exact congrArg ((1 / (2 * Real.pi * I) : ℂ) • ·) hraw

/-- The reflected lower horizontal edge also vanishes. -/
theorem tendsto_pintzSourceWeight_HIntegral'_neg_zero
    {rho : ℂ} {lambda h : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda (-R))
      atTop (nhds 0) := by
  have hlambdaPos : 0 < lambda := by linarith
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun R => by
      simpa only [neg_sq] using
        norm_pintzSourceWeight_HIntegral'_le
          (R := -R) hrho hlambda)
  have hgauss : Tendsto
      (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := tendsto_pintzGaussian_ordinate_zero hlambdaPos
  simpa only [mul_assoc, mul_zero] using hgauss.const_mul
    ((lambda - 3) * hughesYoungZetaHalfPlaneMajorant *
      Real.exp (lambda + |h| * lambda))

/-- Complete residue-free displacement of Pintz's individual weight from
`Re s = 3` to `Re s = lambda`. -/
theorem pintzSourceWeight_complete_vertical_shift
    {rho : ℂ} {lambda h : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) :
    VerticalIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 =
      VerticalIntegral' (pintzSourceWeightIntegrand rho lambda h) lambda := by
  have hlambdaPos : 0 < lambda := by linarith
  have hright := tendsto_pintzSourceWeight_VIntegral'_verticalIntegral'
    (h := h) hrho hlambdaPos hlambda
  have hleft := tendsto_pintzSourceWeight_VIntegral'_verticalIntegral'
    (h := h) (c := 3) hrho hlambdaPos (by norm_num)
  have htop := tendsto_pintzSourceWeight_HIntegral'_zero
    (h := h) hrho hlambda
  have hbottom := tendsto_pintzSourceWeight_HIntegral'_neg_zero
    (h := h) hrho hlambda
  have hrhs : Tendsto (fun R : ℝ =>
      VIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 (-R) R -
        HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda (-R) +
        HIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 lambda R)
      atTop
      (nhds (VerticalIntegral'
        (pintzSourceWeightIntegrand rho lambda h) 3)) := by
    simpa using (hleft.sub hbottom).add htop
  exact (tendsto_nhds_unique hright (hrhs.congr'
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
      exact (pintzSourceWeight_finite_vertical_shift
        (rho := rho) (h := h) hrho hlambda hR).symm))).symm

/-- Source-facing equation (4.4): the weight itself may be evaluated on the
far-right line. -/
theorem pintzSourceWeight_eq_rightLine
    {rho : ℂ} {lambda h : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) :
    pintzSourceWeight rho lambda h =
      VerticalIntegral' (pintzSourceWeightIntegrand rho lambda h) lambda := by
  change VerticalIntegral' (pintzSourceWeightIntegrand rho lambda h) 3 = _
  exact pintzSourceWeight_complete_vertical_shift hrho hlambda

/-- Explicit complete right-line bound for `w_ρ(h)`.  This retains the
Gaussian integral factor, so no asymptotic constant is hidden. -/
theorem norm_pintzSourceWeight_le_rightLine
    {rho : ℂ} {lambda h : ℝ}
    (hrho : 1 / 2 <= rho.re) (hlambda : 3 <= lambda) :
    ‖pintzSourceWeight rho lambda h‖ <=
      hughesYoungZetaHalfPlaneMajorant *
        Real.exp (lambda + h * lambda) *
          Real.sqrt (Real.pi / (1 / lambda)) := by
  have hlambdaPos : 0 < lambda := by linarith
  rw [pintzSourceWeight_eq_rightLine hrho hlambda]
  have hint := integrable_pintzSourceWeightIntegrand_vertical
    (h := h) hrho hlambdaPos hlambda
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambdaPos)
  have hupper : Integrable (fun t : ℝ =>
      (hughesYoungZetaHalfPlaneMajorant *
        Real.exp (lambda + h * lambda)) *
          Real.exp (-(1 / lambda) * t ^ 2)) :=
    hgaussian.const_mul
      (hughesYoungZetaHalfPlaneMajorant *
        Real.exp (lambda + h * lambda))
  have hmono :
      ∫ t : ℝ, ‖pintzSourceWeightIntegrand rho lambda h
          ((lambda : ℂ) + (t : ℂ) * I)‖ <=
        ∫ t : ℝ,
          (hughesYoungZetaHalfPlaneMajorant *
            Real.exp (lambda + h * lambda)) *
              Real.exp (-(1 / lambda) * t ^ 2) := by
    apply integral_mono hint.norm hupper
    intro t
    simpa [show lambda ^ 2 / lambda = lambda by field_simp] using
      norm_pintzSourceWeightIntegrand_vertical_le
        (t := t) hrho hlambdaPos hlambda
  have hnormIntegral :
      ‖∫ t : ℝ, pintzSourceWeightIntegrand rho lambda h
          ((lambda : ℂ) + (t : ℂ) * I)‖ <=
        ∫ t : ℝ, ‖pintzSourceWeightIntegrand rho lambda h
          ((lambda : ℂ) + (t : ℂ) * I)‖ :=
    norm_integral_le_integral_norm _
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul, norm_I]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
          (1 * ‖∫ t : ℝ, pintzSourceWeightIntegrand rho lambda h
            ((lambda : ℂ) + (t : ℂ) * I)‖)
        <= 1 * (1 * (∫ t : ℝ,
          ‖pintzSourceWeightIntegrand rho lambda h
            ((lambda : ℂ) + (t : ℂ) * I)‖)) := by
      exact mul_le_mul norm_pintzWeight_normalization_le_one
        (mul_le_mul_of_nonneg_left hnormIntegral (by norm_num))
        (by positivity) (by positivity)
    _ <= ∫ t : ℝ,
          (hughesYoungZetaHalfPlaneMajorant *
            Real.exp (lambda + h * lambda)) *
              Real.exp (-(1 / lambda) * t ^ 2) := by
      simpa using hmono
    _ = hughesYoungZetaHalfPlaneMajorant *
        Real.exp (lambda + h * lambda) *
          Real.sqrt (Real.pi / (1 / lambda)) := by
      rw [integral_const_mul, integral_gaussian]

#print axioms pintzSourceWeight_complete_vertical_shift
#print axioms pintzSourceWeight_eq_rightLine
#print axioms norm_pintzSourceWeight_le_rightLine

#print axioms norm_pintzSourceWeightNumerator_vertical
#print axioms integrable_pintzSourceWeightIntegrand_vertical

end

end GafniTao
