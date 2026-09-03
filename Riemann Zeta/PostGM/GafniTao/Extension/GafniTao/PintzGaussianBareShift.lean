import GafniTao.PintzGaussianContour

/-!
# The bare Gaussian displacement in Pintz equation (4.1)

This file passes from the finite rectangle identity to complete vertical
lines.  The two horizontal edges are retained quantitatively until their
Gaussian decay has been proved.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

noncomputable section

/-- Uniform pointwise decay of the bare Pintz kernel on either horizontal
edge of the fixed strip `-3 <= re s <= 3`. -/
theorem norm_pintzGaussianKernel_horizontal_le
    {lambda x R : ℝ} (hlambda : 0 < lambda)
    (hxLower : -3 <= x) (hxUpper : x <= 3) (hR : 1 <= |R|) :
    ‖pintzGaussianKernel lambda ((x : ℂ) + (R : ℂ) * I)‖ <=
      Real.exp (9 / lambda + 3 * lambda) *
        Real.exp (-(1 / lambda) * R ^ 2) := by
  rw [pintzGaussianKernel, norm_div]
  have hnum :
      ‖pintzGaussianNumerator lambda ((x : ℂ) + (R : ℂ) * I)‖ <=
        Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2) := by
    rw [show (R : ℂ) * I = I * R by simp [mul_comm]]
    rw [norm_pintzGaussianNumerator_vertical_factored lambda x R hlambda]
    rw [mul_le_mul_iff_of_pos_right (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hxSq : x ^ 2 <= 9 := by nlinarith
    have hxDiv : x ^ 2 / lambda <= 9 / lambda :=
      (div_le_div_iff_of_pos_right hlambda).mpr hxSq
    nlinarith
  have hden : 1 <= ‖(x : ℂ) + (R : ℂ) * I‖ := by
    have him : |R| <= ‖(x : ℂ) + (R : ℂ) * I‖ := by
      simpa using Complex.abs_im_le_norm ((x : ℂ) + (R : ℂ) * I)
    exact hR.trans him
  exact (div_le_self (norm_nonneg _) hden).trans hnum

/-- Both normalized horizontal edges of the fixed strip have an explicit
Gaussian majorant. -/
theorem norm_pintzGaussian_HIntegral'_le
    {lambda R : ℝ} (hlambda : 0 < lambda) (hR : 1 <= |R|) :
    ‖HIntegral' (pintzGaussianKernel lambda) (-3) 3 R‖ <=
      6 * (Real.exp (9 / lambda + 3 * lambda) *
        Real.exp (-(1 / lambda) * R ^ 2)) := by
  have hbase :
      ‖HIntegral (pintzGaussianKernel lambda) (-3) 3 R‖ <=
        (Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |3 - (-3 : ℝ)| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (-3 : ℝ) 3 := by
      rw [← Set.uIcc_of_le (by norm_num : (-3 : ℝ) <= 3)]
      exact Set.uIoc_subset_uIcc hx
    simpa only [ofReal_mul, ofReal_neg, ofReal_ofNat] using
      norm_pintzGaussianKernel_horizontal_le hlambda hx'.1 hx'.2 hR
  unfold HIntegral'
  rw [norm_smul]
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ <= 1 := by
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
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (pintzGaussianKernel lambda) (-3) 3 R‖
        <= 1 * ((Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) * |3 - (-3 : ℝ)|) :=
      mul_le_mul hscalar hbase (norm_nonneg _) (by positivity)
    _ = 6 * (Real.exp (9 / lambda + 3 * lambda) *
        Real.exp (-(1 / lambda) * R ^ 2)) := by ring_nf

/-- The Gaussian ordinate in the horizontal-edge bound tends to zero. -/
theorem tendsto_pintzGaussian_ordinate_zero
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun R : ℝ => Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := by
  have hquad : Tendsto (fun R : ℝ => (1 / lambda) * R ^ 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (max 1 (max 0 (b * lambda)))] with R hR
    have hR1 : 1 <= R := (le_max_left _ _).trans hR
    have hRb : b * lambda <= R :=
      (le_max_right 0 (b * lambda)).trans
        ((le_max_right 1 (max 0 (b * lambda))).trans hR)
    have hR0 : 0 <= R := zero_le_one.trans hR1
    have hRSq : R <= R ^ 2 := by nlinarith
    have hbMul : b * lambda <= R ^ 2 := hRb.trans hRSq
    calc
      b = (b * lambda) / lambda := by field_simp
      _ <= R ^ 2 / lambda :=
        (div_le_div_iff_of_pos_right hlambda).2 hbMul
      _ = (1 / lambda) * R ^ 2 := by ring
  simpa only [Function.comp_apply, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hquad

/-- Each normalized horizontal edge vanishes as the rectangle height tends
to infinity. -/
theorem tendsto_pintzGaussian_HIntegral'_zero
    {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintzGaussianKernel lambda) (-3) 3 R)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ R : ℝ in atTop,
      ‖HIntegral' (pintzGaussianKernel lambda) (-3) 3 R‖ <=
        6 * (Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact norm_pintzGaussian_HIntegral'_le hlambda
        (by simpa [abs_of_nonneg (zero_le_one.trans hR)] using hR))
  simpa only [mul_assoc, mul_zero] using
    (tendsto_pintzGaussian_ordinate_zero hlambda).const_mul
      (6 * Real.exp (9 / lambda + 3 * lambda))

/-- Truncating a complete normalized vertical line symmetrically converges
to the source-facing complete vertical integral. -/
theorem tendsto_pintzGaussian_VIntegral'_verticalIntegral'
    {lambda c : ℝ} (hlambda : 0 < lambda) (hc : c ≠ 0) :
    Tendsto (fun R : ℝ =>
      VIntegral' (pintzGaussianKernel lambda) c (-R) R)
      atTop (nhds (VerticalIntegral' (pintzGaussianKernel lambda) c)) := by
  have hint := intervalIntegral_tendsto_integral
    (integrable_pintzGaussianKernel_vertical lambda c hlambda hc)
    tendsto_neg_atTop_atBot tendsto_id
  unfold VIntegral' VIntegral VerticalIntegral'
  unfold VerticalIntegral
  have hint' : Tendsto (fun R : ℝ =>
      ∫ y in (-R)..R,
        pintzGaussianKernel lambda ((c : ℂ) + (y : ℂ) * I))
      atTop (nhds (∫ t : ℝ,
        pintzGaussianKernel lambda ((c : ℂ) + (t : ℂ) * I))) := by
    simpa only [id_eq, mul_comm] using hint
  exact Tendsto.smul tendsto_const_nhds
    (Tendsto.smul tendsto_const_nhds hint')

/-- Complete bare contour displacement: this is the exact infinite-height
identity underlying Pintz (4.1), before estimating the left line. -/
theorem pintzGaussian_complete_vertical_shift
    {lambda : ℝ} (hlambda : 0 < lambda) :
    VerticalIntegral' (pintzGaussianKernel lambda) 3 =
      1 + VerticalIntegral' (pintzGaussianKernel lambda) (-3) := by
  have hright := tendsto_pintzGaussian_VIntegral'_verticalIntegral'
    hlambda (by norm_num : (3 : ℝ) ≠ 0)
  have hleft := tendsto_pintzGaussian_VIntegral'_verticalIntegral'
    hlambda (by norm_num : (-3 : ℝ) ≠ 0)
  have htop := tendsto_pintzGaussian_HIntegral'_zero hlambda
  have hbottom : Tendsto (fun R : ℝ =>
      HIntegral' (pintzGaussianKernel lambda) (-3) 3 (-R))
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (show ∀ᶠ R : ℝ in atTop,
        ‖HIntegral' (pintzGaussianKernel lambda) (-3) 3 (-R)‖ <=
          6 * (Real.exp (9 / lambda + 3 * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2)) by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
        simpa only [neg_sq, abs_neg] using
          norm_pintzGaussian_HIntegral'_le hlambda
            (R := -R)
            (by simpa [abs_of_nonneg (zero_le_one.trans hR)] using hR))
    simpa only [mul_assoc, mul_zero] using
      (tendsto_pintzGaussian_ordinate_zero hlambda).const_mul
        (6 * Real.exp (9 / lambda + 3 * lambda))
  have hrhs : Tendsto (fun R : ℝ =>
      1 - HIntegral' (pintzGaussianKernel lambda) (-3) 3 (-R) +
        HIntegral' (pintzGaussianKernel lambda) (-3) 3 R +
          VIntegral' (pintzGaussianKernel lambda) (-3) (-R) R)
      atTop
      (nhds (1 + VerticalIntegral' (pintzGaussianKernel lambda) (-3))) := by
    simpa using ((tendsto_const_nhds.sub hbottom).add htop).add hleft
  exact tendsto_nhds_unique hright (hrhs.congr'
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact (pintzGaussian_rightVertical_eq_one_add_edges
        (lambda := lambda) (left := -3) (right := 3)
        (by norm_num) (by norm_num) hR).symm))

private theorem norm_pintzGaussian_normalization_le_one :
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

/-- Pointwise majorization of the left line in Pintz (4.1). -/
theorem norm_pintzGaussianKernel_left_le
    {lambda t : ℝ} (hlambda : 0 < lambda) :
    ‖pintzGaussianKernel lambda ((-3 : ℝ) + (t : ℂ) * I)‖ <=
      (1 / 3 : ℝ) *
        (Real.exp (9 / lambda - 3 * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2)) := by
  rw [pintzGaussianKernel, norm_div]
  have hden : (3 : ℝ) <= ‖((-3 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    have hre := Complex.abs_re_le_norm
      (((-3 : ℝ) : ℂ) + (t : ℂ) * I)
    norm_num at hre ⊢
    exact hre
  calc
    ‖pintzGaussianNumerator lambda
        (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖ /
        ‖((-3 : ℝ) : ℂ) + (t : ℂ) * I‖
        <= ‖pintzGaussianNumerator lambda
            (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖ / 3 := by
          exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden
    _ = (1 / 3 : ℝ) *
        (Real.exp (9 / lambda - 3 * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2)) := by
      rw [show (t : ℂ) * I = I * t by simp [mul_comm]]
      rw [norm_pintzGaussianNumerator_vertical_factored lambda (-3) t hlambda]
      ring_nf

/-- Explicit complete-left-line bound before the elementary absorption of
the square-root factor. -/
theorem norm_pintzGaussian_leftVertical_le
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ‖VerticalIntegral' (pintzGaussianKernel lambda) (-3)‖ <=
      (1 / 3 : ℝ) * Real.exp (9 / lambda - 3 * lambda) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
  have hkernel := integrable_pintzGaussianKernel_vertical
    lambda (-3) hlambda (by norm_num)
  have hkernel' : Integrable (fun t : ℝ =>
      pintzGaussianKernel lambda
        (((-3 : ℝ) : ℂ) + (t : ℂ) * I)) := by
    simpa only [mul_comm] using hkernel
  have hgaussian : Integrable
      (fun t : ℝ => Real.exp (-(1 / lambda) * t ^ 2)) :=
    integrable_exp_neg_mul_sq (one_div_pos.mpr hlambda)
  have hupper : Integrable (fun t : ℝ =>
      (1 / 3 : ℝ) *
        (Real.exp (9 / lambda - 3 * lambda) *
          Real.exp (-(1 / lambda) * t ^ 2))) :=
    (hgaussian.const_mul (Real.exp (9 / lambda - 3 * lambda))).const_mul
      (1 / 3 : ℝ)
  have hmono :
      ∫ t : ℝ, ‖pintzGaussianKernel lambda
          (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖ <=
        ∫ t : ℝ, (1 / 3 : ℝ) *
          (Real.exp (9 / lambda - 3 * lambda) *
            Real.exp (-(1 / lambda) * t ^ 2)) := by
    apply integral_mono hkernel'.norm hupper
    intro t
    exact norm_pintzGaussianKernel_left_le hlambda
  have hnormIntegral :
      ‖∫ t : ℝ, pintzGaussianKernel lambda
          (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖ <=
        ∫ t : ℝ, ‖pintzGaussianKernel lambda
          (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
    norm_integral_le_integral_norm _
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul, norm_mul, norm_I]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        (1 * ‖∫ t : ℝ, pintzGaussianKernel lambda
          (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        <= 1 * (1 * (∫ t : ℝ, ‖pintzGaussianKernel lambda
          (((-3 : ℝ) : ℂ) + (t : ℂ) * I)‖)) := by
      exact mul_le_mul norm_pintzGaussian_normalization_le_one
        (mul_le_mul_of_nonneg_left hnormIntegral (by norm_num))
        (by positivity) (by positivity)
    _ <= ∫ t : ℝ, (1 / 3 : ℝ) *
          (Real.exp (9 / lambda - 3 * lambda) *
            Real.exp (-(1 / lambda) * t ^ 2)) := by simpa using hmono
    _ = (1 / 3 : ℝ) * Real.exp (9 / lambda - 3 * lambda) *
        Real.sqrt (Real.pi / (1 / lambda)) := by
      rw [integral_const_mul, integral_const_mul, integral_gaussian]
      ring

/-- For the range used in Pintz, the complete left line is at most the
paper's `Y^-2` error after writing `lambda = log Y`. -/
theorem norm_pintzGaussian_leftVertical_le_exp_neg_two
    {lambda : ℝ} (hlambda : 8 <= lambda) :
    ‖VerticalIntegral' (pintzGaussianKernel lambda) (-3)‖ <=
      Real.exp (-2 * lambda) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hbase := norm_pintzGaussian_leftVertical_le hlambdaPos
  have hpiLambda : Real.pi * lambda <= lambda ^ 2 := by
    have hpi : Real.pi <= lambda := by nlinarith [Real.pi_lt_four]
    nlinarith
  have hsqrt : Real.sqrt (Real.pi / (1 / lambda)) <= lambda := by
    rw [show Real.pi / (1 / lambda) = Real.pi * lambda by field_simp]
    rw [Real.sqrt_le_iff]
    exact ⟨hlambdaPos.le, hpiLambda⟩
  have hlambdaExp : lambda <= Real.exp (lambda / 2) := by
    have hpow := Real.quadratic_le_exp_of_nonneg
      (by positivity : 0 <= lambda / 2)
    nlinarith [sq_nonneg (lambda - 8)]
  have hsqrtExp : Real.sqrt (Real.pi / (1 / lambda)) <=
      Real.exp (lambda / 2) := hsqrt.trans hlambdaExp
  have hfactor : (1 / 3 : ℝ) <= 1 := by norm_num
  have hprod :
      (1 / 3 : ℝ) * Real.exp (9 / lambda - 3 * lambda) *
          Real.sqrt (Real.pi / (1 / lambda)) <=
        Real.exp (9 / lambda - 3 * lambda) * Real.exp (lambda / 2) := by
    calc
      (1 / 3 : ℝ) * Real.exp (9 / lambda - 3 * lambda) *
          Real.sqrt (Real.pi / (1 / lambda))
          <= 1 * Real.exp (9 / lambda - 3 * lambda) *
            Real.sqrt (Real.pi / (1 / lambda)) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hfactor (Real.exp_nonneg _))
                (Real.sqrt_nonneg _)
      _ = Real.exp (9 / lambda - 3 * lambda) *
          Real.sqrt (Real.pi / (1 / lambda)) := by ring
      _ <= Real.exp (9 / lambda - 3 * lambda) *
          Real.exp (lambda / 2) := by gcongr
  calc
    ‖VerticalIntegral' (pintzGaussianKernel lambda) (-3)‖
        <= (1 / 3 : ℝ) * Real.exp (9 / lambda - 3 * lambda) *
          Real.sqrt (Real.pi / (1 / lambda)) := hbase
    _ <= Real.exp (9 / lambda - 3 * lambda) *
        Real.exp (lambda / 2) := hprod
    _ = Real.exp (9 / lambda - 3 * lambda + lambda / 2) := by
      rw [← Real.exp_add]
    _ <= Real.exp (-2 * lambda) := by
      apply Real.exp_le_exp.mpr
      have hrecip : 9 / lambda <= lambda / 2 := by
        rw [div_le_iff₀ hlambdaPos]
        nlinarith [sq_nonneg (lambda - 8)]
      linarith

/-- Pintz equation (4.1), quantitatively and without asymptotic notation. -/
theorem pintz_equation_4_1
    {lambda : ℝ} (hlambda : 8 <= lambda) :
    ‖VerticalIntegral' (pintzGaussianKernel lambda) 3 - 1‖ <=
      Real.exp (-2 * lambda) := by
  rw [pintzGaussian_complete_vertical_shift (by linarith : 0 < lambda)]
  simpa using norm_pintzGaussian_leftVertical_le_exp_neg_two hlambda

#print axioms norm_pintzGaussian_HIntegral'_le
#print axioms pintzGaussian_complete_vertical_shift
#print axioms pintz_equation_4_1

end

end GafniTao
