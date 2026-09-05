import GafniTao.Pintz2023MellinEdges
import RiemannZeta.GuthMaynard.ZetaBounds

/-!
# Pintz (2023), Lemma 3.4: horizontal-edge decay

The finite contour is sent to infinite height using a uniform polynomial
Gamma estimate on `0 ≤ Re w ≤ 2`.  This is enough because zeta has only
linear growth on the corresponding positive real strip.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintz2023_Gamma_positive_strip_decay
    {a t : ℝ} (haLower : 0 ≤ a) (haUpper : a ≤ 2) :
    |t| ^ 3 * ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 := by
  by_cases ht : t = 0
  · subst t
    norm_num
  let z : ℂ := (a : ℂ) + (t : ℂ) * I
  have hzFactor : ∀ j < (3 : ℕ), z + (j : ℂ) ≠ 0 := by
    intro j hj hzero
    have him := congrArg Complex.im hzero
    simp [z, ht] at him
  have hRec := Gamma_add_nat_eq_prod_mul z 3 hzFactor
  have hNormRec :
      ‖Complex.Gamma (z + 3)‖ =
        ‖∏ j ∈ Finset.range 3, (z + (j : ℂ))‖ * ‖Complex.Gamma z‖ := by
    have hRec' : Complex.Gamma (z + 3) =
        (∏ j ∈ Finset.range 3, (z + (j : ℂ))) * Complex.Gamma z := by
      simpa using hRec
    rw [hRec', norm_mul]
  have hProd : |t| ^ 3 ≤ ‖∏ j ∈ Finset.range 3, (z + (j : ℂ))‖ := by
    simpa [z] using abs_im_pow_le_norm_prod_horizontal a t 3
  have hShiftRe : (z + 3).re = a + 3 := by simp [z]
  have hShiftPos : 0 < (z + 3).re := by rw [hShiftRe]; linarith
  have hNormShift : ‖Complex.Gamma (z + 3)‖ ≤ Real.Gamma (a + 3) := by
    simpa [hShiftRe] using Complex.Gamma.norm_le_Gamma_re hShiftPos
  have hThree : (3 : ℝ) ≤ a + 3 := by linarith
  have hFive : a + 3 ≤ (5 : ℝ) := by linarith
  have hGammaMono : Real.Gamma (a + 3) ≤ Real.Gamma 5 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn
      (by linarith : (2 : ℝ) ≤ a + 3) (by norm_num) hFive
  have hGammaFive : Real.Gamma 5 = 24 := by
    convert Real.Gamma_nat_eq_factorial 4 using 1
    norm_num
  have hShift : ‖Complex.Gamma (z + 3)‖ ≤ 24 :=
    hNormShift.trans (hGammaMono.trans_eq hGammaFive)
  rw [hNormRec] at hShift
  have hGap := mul_nonneg (sub_nonneg.mpr hProd)
    (norm_nonneg (Complex.Gamma z))
  nlinarith

theorem pintz2023_Gamma_positive_strip_norm_le
    {a t : ℝ} (haLower : 0 ≤ a) (haUpper : a ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * I)‖ ≤ 24 / |t| ^ 3 := by
  have htPos : 0 < |t| := zero_lt_one.trans_le ht
  apply (le_div_iff₀ (pow_pos htPos 3)).2
  simpa [mul_comm] using
    pintz2023_Gamma_positive_strip_decay haLower haUpper

theorem norm_pintz2023MellinPowerDiff_horizontal_le
    {N : ℕ} (hN : 0 < N) {x y : ℝ}
    (hxUpper : x ≤ 2) :
    ‖pintz2023MellinPowerDiff N ((x : ℂ) + (y : ℂ) * I)‖ ≤
      5 * (N : ℝ) ^ 2 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hTwoNreal : (0 : ℝ) < 2 * N := by positivity
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hTwoNOne : (1 : ℝ) ≤ 2 * N := by nlinarith
  have hTwoPow :
      ‖(((2 * N : ℕ) : ℂ) ^ (((x : ℂ) + (y : ℂ) * I)))‖ ≤
        ((2 * N : ℕ) : ℝ) ^ 2 := by
    rw [show ((2 * N : ℕ) : ℂ) = (((2 * N : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hTwoNreal)]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero,
      zero_mul, sub_self, add_zero]
    simpa [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hTwoNOne hxUpper
  have hOnePow :
      ‖((N : ℂ) ^ (((x : ℂ) + (y : ℂ) * I)))‖ ≤ (N : ℝ) ^ 2 := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hNreal]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero,
      zero_mul, sub_self, add_zero]
    simpa [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le hNOne hxUpper
  unfold pintz2023MellinPowerDiff
  calc
    ‖((2 * N : ℕ) : ℂ) ^ ((x : ℂ) + (y : ℂ) * I) -
        (N : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ ≤
      ‖((2 * N : ℕ) : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ +
        ‖(N : ℂ) ^ ((x : ℂ) + (y : ℂ) * I)‖ := norm_sub_le _ _
    _ ≤ ((2 * N : ℕ) : ℝ) ^ 2 + (N : ℝ) ^ 2 := add_le_add hTwoPow hOnePow
    _ = 5 * (N : ℝ) ^ 2 := by push_cast; ring

noncomputable def pintz2023MellinHorizontalSize (s : ℂ) (R : ℝ) : ℝ :=
  |s.re| + 2 + |s.im| + |R|

theorem norm_pintz2023MellinContourIntegrand_horizontal_le
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 1 / 4 ≤ s.re)
    {x R : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2)
    (hR : 1 ≤ |R|) (hheight : 1 ≤ |s.im + R|) :
    ‖pintz2023MellinContourIntegrand N s
        ((x : ℂ) + (R : ℂ) * I)‖ ≤
      (5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
        (5 * pintz2023MellinHorizontalSize s R) := by
  have hw : ((x : ℂ) + (R : ℂ) * I) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp at him
    have hRabsPos : 0 < |R| := zero_lt_one.trans_le hR
    have hRne : R ≠ 0 := abs_pos.mp hRabsPos
    exact hRne him
  rw [pintz2023MellinContourIntegrand_eq_source hw,
    norm_mul, norm_mul]
  have hPower := norm_pintz2023MellinPowerDiff_horizontal_le
    (y := R) hN hx.2
  have hGamma := pintz2023_Gamma_positive_strip_norm_le hx.1 hx.2 hR
  have hzetaRe : (1 / 4 : ℝ) ≤ (s + ((x : ℂ) + (R : ℂ) * I)).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero,
      zero_mul, sub_self, add_zero]
    linarith [hx.1]
  have hzetaIm : 1 ≤ |(s + ((x : ℂ) + (R : ℂ) * I)).im| := by
    simpa using hheight
  have hzeta := norm_riemannZeta_le_five_mul_norm hzetaRe hzetaIm
  have hnorm :
      ‖s + ((x : ℂ) + (R : ℂ) * I)‖ ≤
        pintz2023MellinHorizontalSize s R := by
    calc
      ‖s + ((x : ℂ) + (R : ℂ) * I)‖ ≤
          |(s + ((x : ℂ) + (R : ℂ) * I)).re| +
            |(s + ((x : ℂ) + (R : ℂ) * I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |s.re + x| + |s.im + R| := by
        congr 1 <;> simp
      _ ≤ (|s.re| + |x|) + (|s.im| + |R|) := by
        gcongr <;> exact abs_add_le _ _
      _ ≤ (|s.re| + 2) + (|s.im| + |R|) := by
        gcongr
        rw [abs_of_nonneg hx.1]
        exact hx.2
      _ = pintz2023MellinHorizontalSize s R := by
        simp only [pintz2023MellinHorizontalSize]
        ring
  calc
    ‖pintz2023MellinPowerDiff N ((x : ℂ) + (R : ℂ) * I)‖ *
        ‖Complex.Gamma ((x : ℂ) + (R : ℂ) * I)‖ *
        ‖riemannZeta (s + ((x : ℂ) + (R : ℂ) * I))‖ ≤
      (5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
        (5 * ‖s + ((x : ℂ) + (R : ℂ) * I)‖) := by
      apply mul_le_mul
      · exact mul_le_mul hPower hGamma (norm_nonneg _)
          (by positivity)
      · exact hzeta
      · exact norm_nonneg _
      · positivity
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hnorm (by norm_num)
      · positivity

theorem norm_pintz2023Mellin_HIntegral'_le
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 1 / 4 ≤ s.re)
    {R : ℝ} (hR : 1 ≤ |R|) (hheight : 1 ≤ |s.im + R|) :
    ‖HIntegral' (pintz2023MellinContourIntegrand N s) 0 2 R‖ ≤
      2 * ((5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
        (5 * pintz2023MellinHorizontalSize s R)) := by
  let M : ℝ := (5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
    (5 * pintz2023MellinHorizontalSize s R)
  have hbase :
      ‖HIntegral (pintz2023MellinContourIntegrand N s) 0 2 R‖ ≤
        M * |(2 : ℝ) - 0| := by
    unfold HIntegral
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 2 := by
      rw [← Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Set.uIoc_subset_uIcc hx
    exact norm_pintz2023MellinContourIntegrand_horizontal_le
      hN hs hx' hR hheight
  have hscalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real,
      Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hpi : (1 : ℝ) ≤ Real.pi := by nlinarith [Real.pi_gt_three]
    have hpiInv : Real.pi⁻¹ ≤ (1 : ℝ) :=
      (inv_le_one₀ Real.pi_pos).2 hpi
    nlinarith [mul_le_mul_of_nonneg_right hpiInv
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  unfold HIntegral'
  rw [norm_smul]
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (pintz2023MellinContourIntegrand N s) 0 2 R‖ ≤
      1 * (M * |(2 : ℝ) - 0|) :=
        mul_le_mul hscalar hbase (norm_nonneg _) (by positivity)
    _ = 2 * ((5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
        (5 * pintz2023MellinHorizontalSize s R)) := by
      dsimp only [M]
      norm_num
      ring

theorem tendsto_pintz2023Mellin_HIntegral'_zero
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 1 / 4 ≤ s.re) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023MellinContourIntegrand N s) 0 2 R)
      atTop (nhds 0) := by
  let D : ℝ := |s.re| + 2 + |s.im|
  let C : ℝ := 2 * (5 * (N : ℝ) ^ 2) * 24 * 5 * 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ => C * (R⁻¹) ^ 2)
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (max 1 (max D (|s.im| + 1)))] with R hR
    have hRone : 1 ≤ R := (le_max_left _ _).trans hR
    have hDR : D ≤ R := (le_max_left D (|s.im| + 1)).trans
      ((le_max_right 1 _).trans hR)
    have hHeightR : |s.im| + 1 ≤ R :=
      (le_max_right D (|s.im| + 1)).trans ((le_max_right 1 _).trans hR)
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    have hheight : 1 ≤ |s.im + R| := by
      rw [abs_of_nonneg (by linarith [neg_abs_le s.im])]
      linarith [neg_abs_le s.im]
    have hsize : pintz2023MellinHorizontalSize s R ≤ 2 * R := by
      unfold pintz2023MellinHorizontalSize
      rw [abs_of_pos hRpos]
      dsimp only [D] at hDR
      linarith
    have hraw := norm_pintz2023Mellin_HIntegral'_le
      hN hs (R := R) (by simpa [abs_of_pos hRpos] using hRone) hheight
    calc
      ‖HIntegral' (pintz2023MellinContourIntegrand N s) 0 2 R‖ ≤
          2 * ((5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
            (5 * pintz2023MellinHorizontalSize s R)) := hraw
      _ ≤ 2 * ((5 * (N : ℝ) ^ 2) * (24 / |R| ^ 3) *
            (5 * (2 * R))) := by
        gcongr
      _ = C * (R⁻¹) ^ 2 := by
        rw [abs_of_pos hRpos]
        dsimp only [C]
        field_simp
  · have hConst : Tendsto (fun _ : ℝ => C) atTop (nhds C) := tendsto_const_nhds
    simpa using hConst.mul (tendsto_inv_atTop_zero.pow 2)

theorem tendsto_pintz2023Mellin_HIntegral'_neg_zero
    {N : ℕ} {s : ℂ} (hN : 0 < N) (hs : 1 / 4 ≤ s.re) :
    Tendsto (fun R : ℝ =>
      HIntegral' (pintz2023MellinContourIntegrand N s) 0 2 (-R))
      atTop (nhds 0) := by
  let D : ℝ := |s.re| + 2 + |s.im|
  let C : ℝ := 2 * (5 * (N : ℝ) ^ 2) * 24 * 5 * 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun R : ℝ => C * (R⁻¹) ^ 2)
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (max 1 (max D (|s.im| + 1)))] with R hR
    have hRone : 1 ≤ R := (le_max_left _ _).trans hR
    have hDR : D ≤ R := (le_max_left D (|s.im| + 1)).trans
      ((le_max_right 1 _).trans hR)
    have hHeightR : |s.im| + 1 ≤ R :=
      (le_max_right D (|s.im| + 1)).trans ((le_max_right 1 _).trans hR)
    have hRpos : 0 < R := zero_lt_one.trans_le hRone
    have hheight : 1 ≤ |s.im - R| := by
      have habsRaw := abs_sub_abs_le_abs_sub R s.im
      rw [abs_of_pos hRpos] at habsRaw
      have habs : R - |s.im| ≤ |s.im - R| := by
        rw [abs_sub_comm]
        linarith
      linarith
    have hsize : pintz2023MellinHorizontalSize s (-R) ≤ 2 * R := by
      unfold pintz2023MellinHorizontalSize
      rw [abs_neg, abs_of_pos hRpos]
      dsimp only [D] at hDR
      linarith
    have hraw := norm_pintz2023Mellin_HIntegral'_le
      hN hs (R := -R) (by simpa [abs_neg, abs_of_pos hRpos] using hRone)
      (by simpa [sub_eq_add_neg] using hheight)
    calc
      ‖HIntegral' (pintz2023MellinContourIntegrand N s) 0 2 (-R)‖ ≤
          2 * ((5 * (N : ℝ) ^ 2) * (24 / |-R| ^ 3) *
            (5 * pintz2023MellinHorizontalSize s (-R))) := hraw
      _ ≤ 2 * ((5 * (N : ℝ) ^ 2) * (24 / R ^ 3) *
            (5 * (2 * R))) := by
        rw [abs_neg, abs_of_pos hRpos]
        gcongr
      _ = C * (R⁻¹) ^ 2 := by
        dsimp only [C]
        field_simp
  · have hConst : Tendsto (fun _ : ℝ => C) atTop (nhds C) := tendsto_const_nhds
    simpa using hConst.mul (tendsto_inv_atTop_zero.pow 2)

#print axioms pintz2023_Gamma_positive_strip_decay
#print axioms norm_pintz2023MellinPowerDiff_horizontal_le
#print axioms norm_pintz2023MellinContourIntegrand_horizontal_le
#print axioms tendsto_pintz2023Mellin_HIntegral'_zero
#print axioms tendsto_pintz2023Mellin_HIntegral'_neg_zero

end

end GafniTao
