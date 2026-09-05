import GafniTao.Pintz2023Equation42LeftIntegrable
import GafniTao.PintzGaussianBareShift

/-!
# Pintz (2023), equation (4.2): complete horizontal-edge decay

This module bounds the literal product `M_X * zeta` on the full horizontal
edges of the residue rectangle.  The estimate is uniform in the real
coordinate, retains the actual Gaussian kernel, and tends to zero as the
rectangle height tends to infinity.
-/

open Complex Filter MeasureTheory Set Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

set_option maxHeartbeats 800000

noncomputable def pintz2023HorizontalSize
    (rho : ℂ) (left R : ℝ) : ℝ :=
  |rho.re| + max |left| 3 + |rho.im| + |R|

theorem norm_pintz2023Equation42Integrand_horizontal_le
    {X : ℕ} {rho : ℂ} {lambda left x R : ℝ}
    (hlambda : 0 < lambda) (hleftLower : -3 ≤ left)
    (hx : x ∈ Set.Icc left 3)
    (hsigmaLower : 1 / 4 ≤ rho.re + left)
    (hR : 1 ≤ |R|)
    (hheight : 1 ≤ |rho.im + R|) :
    ‖pintz2023Equation42Integrand X rho lambda
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (X : ℝ) * (5 * pintz2023HorizontalSize rho left R) *
        (Real.exp (9 / lambda + 3 * lambda) *
          Real.exp (-(1 / lambda) * R ^ 2)) := by
  let z : ℂ := rho + ((x : ℂ) + (R : ℂ) * I)
  have hzRe : z.re = rho.re + x := by simp [z, Complex.mul_re]
  have hzIm : z.im = rho.im + R := by simp [z, Complex.mul_im]
  have hxLower : -3 ≤ x := hleftLower.trans hx.1
  have hsigma : 1 / 4 ≤ z.re := by
    rw [hzRe]
    exact hsigmaLower.trans (by linarith [hx.1])
  have hmoll : ‖zetaMollifier X z‖ ≤ (X : ℝ) :=
    norm_zetaMollifier_le_length X z (by linarith)
  have hzeta : ‖riemannZeta z‖ ≤ 5 * ‖z‖ :=
    norm_riemannZeta_le_five_mul_norm hsigma (hzIm.symm ▸ hheight)
  have hxAbs : |x| ≤ max |left| 3 := by
    rw [abs_le]
    constructor
    · have hmax : |left| ≤ max |left| 3 := le_max_left _ _
      have hneg : -max |left| 3 ≤ left :=
        (neg_le_neg hmax).trans (neg_abs_le left)
      exact hneg.trans hx.1
    · exact hx.2.trans (le_max_right _ _)
  have hznorm : ‖z‖ ≤ pintz2023HorizontalSize rho left R := by
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ = |rho.re + x| + |rho.im + R| := by rw [hzRe, hzIm]
      _ ≤ (|rho.re| + |x|) + (|rho.im| + |R|) := by
        gcongr <;> exact abs_add_le _ _
      _ ≤ (|rho.re| + max |left| 3) + (|rho.im| + |R|) := by
        gcongr
      _ = pintz2023HorizontalSize rho left R := by
        simp only [pintz2023HorizontalSize]
        ring_nf
  have hkernel := norm_pintzGaussianKernel_horizontal_le hlambda
    hxLower hx.2 hR
  change ‖zetaMollifier X z * riemannZeta z *
      pintzGaussianKernel lambda ((x : ℂ) + (R : ℂ) * I)‖ ≤ _
  rw [norm_mul, norm_mul]
  calc
    ‖zetaMollifier X z‖ * ‖riemannZeta z‖ *
        ‖pintzGaussianKernel lambda ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (X : ℝ) * (5 * ‖z‖) *
        ‖pintzGaussianKernel lambda ((x : ℂ) + (R : ℂ) * I)‖ := by
          gcongr
    _ ≤ (X : ℝ) * (5 * pintz2023HorizontalSize rho left R) *
        ‖pintzGaussianKernel lambda ((x : ℂ) + (R : ℂ) * I)‖ := by
          gcongr
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left hkernel
      exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (by
          unfold pintz2023HorizontalSize
          positivity))

theorem norm_pintz2023Equation42_HIntegral'_le
    {X : ℕ} {rho : ℂ} {lambda left R : ℝ}
    (hlambda : 0 < lambda) (hleftLower : -3 ≤ left)
    (hleftUpper : left ≤ 3)
    (hsigmaLower : 1 / 4 ≤ rho.re + left)
    (hR : 1 ≤ |R|)
    (hheight : 1 ≤ |rho.im + R|) :
    ‖HIntegral' (pintz2023Equation42Integrand X rho lambda)
        left 3 R‖ ≤
      |3 - left| *
        ((X : ℝ) * (5 * pintz2023HorizontalSize rho left R) *
          (Real.exp (9 / lambda + 3 * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2))) := by
  let M : ℝ :=
    (X : ℝ) * (5 * pintz2023HorizontalSize rho left R) *
      (Real.exp (9 / lambda + 3 * lambda) *
        Real.exp (-(1 / lambda) * R ^ 2))
  have hbase :
      ‖HIntegral (pintz2023Equation42Integrand X rho lambda) left 3 R‖ ≤
        M * |3 - left| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc left 3 := by
      rw [← Set.uIcc_of_le hleftUpper]
      exact Set.uIoc_subset_uIcc hx
    exact norm_pintz2023Equation42Integrand_horizontal_le hlambda
      hleftLower hx' hsigmaLower hR hheight
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    nlinarith [mul_le_mul_of_nonneg_right hpiInv (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (pintz2023Equation42Integrand X rho lambda) left 3 R‖ ≤
      1 * (M * |3 - left|) :=
        mul_le_mul hscalar hbase (norm_nonneg _) (by positivity)
    _ = |3 - left| *
        ((X : ℝ) * (5 * pintz2023HorizontalSize rho left R) *
          (Real.exp (9 / lambda + 3 * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2))) := by
      dsimp only [M]
      ring_nf

theorem tendsto_pintz2023HorizontalMajorant_zero
    {rho : ℂ} {lambda left : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun R : ℝ =>
      pintz2023HorizontalSize rho left R *
        Real.exp (-(1 / lambda) * R ^ 2)) atTop (nhds 0) := by
  let D : ℝ := |rho.re| + max |left| 3 + |rho.im|
  have hbaseRpow : Tendsto (fun R : ℝ =>
      R ^ (1 : ℝ) * Real.exp (-(1 / lambda) * R ^ 2))
      atTop (nhds 0) := by
    have hExp : Tendsto (fun R : ℝ => Real.exp (-(1 / 2 : ℝ) * R))
        atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0))
    exact (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (one_div_pos.mpr hlambda) 1).tendsto_zero_of_tendsto hExp
  have hbase : Tendsto (fun R : ℝ =>
      R * Real.exp (-(1 / lambda) * R ^ 2)) atTop (nhds 0) := by
    simpa using hbaseRpow
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ =>
      2 * R * Real.exp (-(1 / lambda) * R ^ 2))
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (max 1 D)] with R hR
    have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
    have hDR : D ≤ R := (le_max_right _ _).trans hR
    have hR0 : 0 ≤ R := zero_le_one.trans hR1
    have hsize : pintz2023HorizontalSize rho left R ≤ 2 * R := by
      unfold pintz2023HorizontalSize
      rw [abs_of_nonneg hR0]
      dsimp only [D] at hDR ⊢
      linarith
    rw [Real.norm_of_nonneg (mul_nonneg (by
      dsimp only [pintz2023HorizontalSize]; positivity) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right hsize (Real.exp_pos _).le
  · simpa only [mul_assoc, mul_zero] using hbase.const_mul (2 : ℝ)

theorem tendsto_pintz2023Equation42_HIntegral'_zero
    {X : ℕ} {rho : ℂ} {lambda left : ℝ}
    (hlambda : 0 < lambda) (hleftLower : -3 ≤ left)
    (hleftUpper : left ≤ 3)
    (hsigmaLower : 1 / 4 ≤ rho.re + left) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023Equation42Integrand X rho lambda) left 3 R)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ =>
      |3 - left| *
        ((X : ℝ) * (5 * pintz2023HorizontalSize rho left R) *
          (Real.exp (9 / lambda + 3 * lambda) *
            Real.exp (-(1 / lambda) * R ^ 2))))
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (|rho.im| + 1)] with R hR
    have hR0 : 0 ≤ R := by linarith [abs_nonneg rho.im]
    have hheight : 1 ≤ |rho.im + R| := by
      have h := abs_sub_abs_le_abs_sub R (-rho.im)
      have h' : R - |rho.im| ≤ |rho.im + R| := by
        simpa [abs_of_nonneg hR0, abs_neg, sub_neg_eq_add, add_comm] using h
      linarith
    have hRabs : 1 ≤ |R| := by
      rw [abs_of_nonneg hR0]
      linarith [abs_nonneg rho.im]
    exact norm_pintz2023Equation42_HIntegral'_le hlambda hleftLower
      hleftUpper hsigmaLower hRabs hheight
  · have hmajor := tendsto_pintz2023HorizontalMajorant_zero
      (rho := rho) (lambda := lambda) (left := left) hlambda
    let C : ℝ := |3 - left| * ((X : ℝ) * 5 *
      Real.exp (9 / lambda + 3 * lambda))
    have hscaled := hmajor.const_mul C
    convert hscaled using 1
    · funext R
      simp only [C]
      ring_nf
    · simp

theorem tendsto_pintz2023Equation42_HIntegral'_neg_zero
    {X : ℕ} {rho : ℂ} {lambda left : ℝ}
    (hlambda : 0 < lambda) (hleftLower : -3 ≤ left)
    (hleftUpper : left ≤ 3)
    (hsigmaLower : 1 / 4 ≤ rho.re + left) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023Equation42Integrand X rho lambda) left 3 (-R))
      atTop (nhds 0) := by
  -- The same direct majorant applies after replacing `R` by `-R`; use it
  -- explicitly so no conjugation identity for the mollifier is required.
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ =>
      |3 - left| *
        ((X : ℝ) * (5 * pintz2023HorizontalSize rho left (-R)) *
          (Real.exp (9 / lambda + 3 * lambda) *
            Real.exp (-(1 / lambda) * (-R) ^ 2))))
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (|rho.im| + 1)] with R hR
    have hR0 : 0 ≤ R := by linarith [abs_nonneg rho.im]
    have hheight : 1 ≤ |rho.im - R| := by
      have habs : |R| - |rho.im| ≤ |rho.im - R| := by
        simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub R rho.im
      rw [abs_of_nonneg hR0] at habs
      linarith
    simpa only [neg_sq, abs_neg] using
      norm_pintz2023Equation42_HIntegral'_le
        (X := X) (rho := rho) (lambda := lambda) (left := left) (R := -R)
        hlambda hleftLower hleftUpper hsigmaLower
        (by rw [abs_neg, abs_of_nonneg hR0]; linarith [abs_nonneg rho.im])
        (by simpa [sub_eq_add_neg] using hheight)
  · have hmajor := tendsto_pintz2023HorizontalMajorant_zero
      (rho := rho) (lambda := lambda) (left := left) hlambda
    let C : ℝ := |3 - left| * ((X : ℝ) * 5 *
      Real.exp (9 / lambda + 3 * lambda))
    have hscaled := hmajor.const_mul C
    convert hscaled using 1
    · funext R
      simp only [C, pintz2023HorizontalSize, abs_neg]
      ring_nf
    · simp

#print axioms norm_pintz2023Equation42Integrand_horizontal_le
#print axioms norm_pintz2023Equation42_HIntegral'_le
#print axioms tendsto_pintz2023HorizontalMajorant_zero
#print axioms tendsto_pintz2023Equation42_HIntegral'_zero
#print axioms tendsto_pintz2023Equation42_HIntegral'_neg_zero

end

end GafniTao
