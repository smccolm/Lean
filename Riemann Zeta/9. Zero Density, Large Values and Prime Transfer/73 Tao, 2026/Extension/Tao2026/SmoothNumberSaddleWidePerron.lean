import Tao2026.SmoothNumberSaddleWideFrequency

/-!
# The principal-phase annulus on the physical Perron line

This module identifies the wide normalized Fourier annulus with the two
literal physical Perron-line segments between the central saddle height and
`pi / log y`.  The standard-deviation substitution is proved with both signs
and endpoints explicit.  Consequently the normalized physical annular
contribution tends to zero in every critical smooth regime, leaving only the
outer tails beyond the principal prime-phase height.
-/

open Filter Topology MeasureTheory Set
open scoped Interval

namespace Tao2026

noncomputable section

theorem smoothSaddleCentralRadius_le_wideRadius
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleCentralRadius X y ≤ smoothSaddleWideRadius X y := by
  have hsigma := smoothSaddlePoint_pos hX hy
  have haPos : 0 < (2 : ℝ) ^ (-smoothSaddlePoint X y) := by positivity
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold smoothSaddleCentralRadius smoothSaddleWideRadius
  have hcoeff : Real.pi / 2 *
      (1 - (2 : ℝ) ^ (-smoothSaddlePoint X y)) ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff hsd.le) hlog.le

theorem integral_smoothSaddleWideAnnularFourierIntegrand_eq_intervalIntegrals
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (∫ t : ℝ, smoothSaddleWideAnnularFourierIntegrand X y t) =
      (∫ t in (-smoothSaddleWideRadius X y)..
          (-smoothSaddleCentralRadius X y),
        smoothSaddleNormalizedCharacteristic X y t *
          smoothSaddleLaplaceFourierKernel X y t) +
      ∫ t in (smoothSaddleCentralRadius X y)..
          (smoothSaddleWideRadius X y),
        smoothSaddleNormalizedCharacteristic X y t *
          smoothSaddleLaplaceFourierKernel X y t := by
  let f : ℝ → ℂ := fun t =>
    smoothSaddleNormalizedCharacteristic X y t *
      smoothSaddleLaplaceFourierKernel X y t
  have hf : Continuous f :=
    (continuous_smoothSaddleNormalizedCharacteristic hX hy).mul
      (continuous_smoothSaddleLaplaceFourierKernel X y)
  have hC := smoothSaddleCentralRadius_pos hX hy
  have hCW := smoothSaddleCentralRadius_le_wideRadius hX hy
  have hdisj : Disjoint
      (Set.Icc (-smoothSaddleWideRadius X y)
        (-smoothSaddleCentralRadius X y))
      (Set.Icc (smoothSaddleCentralRadius X y)
        (smoothSaddleWideRadius X y)) := by
    rw [Set.disjoint_left]
    intro t htL htR
    linarith [htL.2, htR.1]
  unfold smoothSaddleWideAnnularFourierIntegrand
  rw [integral_indicator (measurableSet_Icc.union measurableSet_Icc)]
  rw [MeasureTheory.setIntegral_union₀ hdisj.aedisjoint
    measurableSet_Icc.nullMeasurableSet
    hf.integrableOn_Icc hf.integrableOn_Icc]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le hCW]

/-- The physical Perron-line height corresponding to the full principal
prime-phase radius. -/
noncomputable def smoothSaddleWidePerronHeight (X y : ℕ) : ℝ :=
  smoothSaddleWideRadius X y / smoothSaddleStandardDeviation X y

theorem smoothSaddleWidePerronHeight_eq_pi_div_log
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleWidePerronHeight X y = Real.pi / Real.log (y : ℝ) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  unfold smoothSaddleWidePerronHeight smoothSaddleWideRadius
  field_simp [hsd.ne']

theorem smoothSaddleWidePerronHeight_mul_standardDeviation
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleWidePerronHeight X y *
        smoothSaddleStandardDeviation X y =
      smoothSaddleWideRadius X y := by
  unfold smoothSaddleWidePerronHeight
  field_simp [(smoothSaddleStandardDeviation_pos hX hy).ne']

/-- The standard-deviation substitution on the two physical Perron segments
between the central height and the full principal-phase height. -/
theorem standardDeviation_mul_integral_perronLine_eq_wideAnnularIntervals
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    (smoothSaddleStandardDeviation X y : ℂ) *
        ((∫ t in (-smoothSaddleWidePerronHeight X y)..
              (-smoothSaddleCentralPerronHeight X y),
            smoothSaddlePerronLineIntegrand X y t) +
          ∫ t in (smoothSaddleCentralPerronHeight X y)..
              (smoothSaddleWidePerronHeight X y),
            smoothSaddlePerronLineIntegrand X y t) =
      (∫ u in (-smoothSaddleWideRadius X y)..
            (-smoothSaddleCentralRadius X y),
          smoothSaddleNormalizedCharacteristic X y u *
            smoothSaddleLaplaceFourierKernel X y u) +
        ∫ u in (smoothSaddleCentralRadius X y)..
            (smoothSaddleWideRadius X y),
          smoothSaddleNormalizedCharacteristic X y u *
            smoothSaddleLaplaceFourierKernel X y u := by
  let f : ℝ → ℂ := fun u =>
    smoothSaddleNormalizedCharacteristic X y u *
      smoothSaddleLaplaceFourierKernel X y u
  let Hc := smoothSaddleCentralPerronHeight X y
  let Hw := smoothSaddleWidePerronHeight X y
  let d := smoothSaddleStandardDeviation X y
  have hd : d ≠ 0 := (smoothSaddleStandardDeviation_pos hX hy).ne'
  have hline (t : ℝ) : smoothSaddlePerronLineIntegrand X y t = f (-t * d) :=
    smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy t
  have hleft : (∫ t in (-Hw)..(-Hc), f (-t * d)) =
      ∫ t in Hc..Hw, f (t * d) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun v => f (v * d)) (a := -Hw) (b := -Hc))
  have hright : (∫ t in Hc..Hw, f (-t * d)) =
      ∫ t in (-Hw)..(-Hc), f (t * d) := by
    simpa using (intervalIntegral.integral_comp_neg
      (f := fun v => f (v * d)) (a := Hc) (b := Hw))
  have hscaleLeft := intervalIntegral.smul_integral_comp_mul_right
    (f := f) (a := -Hw) (b := -Hc) d
  have hscaleRight := intervalIntegral.smul_integral_comp_mul_right
    (f := f) (a := Hc) (b := Hw) d
  simp_rw [hline]
  change (d : ℂ) *
      ((∫ t in (-Hw)..(-Hc), f (-t * d)) +
        ∫ t in Hc..Hw, f (-t * d)) = _
  rw [hleft, hright, mul_add, ← Complex.real_smul, ← Complex.real_smul,
    hscaleRight, hscaleLeft]
  have hHc : Hc * d = smoothSaddleCentralRadius X y :=
    smoothSaddleCentralPerronHeight_mul_standardDeviation hX hy
  have hHw : Hw * d = smoothSaddleWideRadius X y :=
    smoothSaddleWidePerronHeight_mul_standardDeviation hX hy
  have hnegHc : (-Hc) * d = -smoothSaddleCentralRadius X y := by
    rw [neg_mul, hHc]
  have hnegHw : (-Hw) * d = -smoothSaddleWideRadius X y := by
    rw [neg_mul, hHw]
  rw [hHc, hHw, hnegHc, hnegHw, add_comm]

/-- The normalized physical Perron contribution of the principal-phase
annulus. -/
noncomputable def smoothSaddleWideAnnularPerronContribution
    (X y : ℕ) : ℂ :=
  ((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-smoothSaddleWidePerronHeight X y)..
          (-smoothSaddleCentralPerronHeight X y),
        smoothSaddlePerronLineIntegrand X y t) +
      ∫ t in (smoothSaddleCentralPerronHeight X y)..
          (smoothSaddleWidePerronHeight X y),
        smoothSaddlePerronLineIntegrand X y t)

theorem smoothSaddleWideAnnularPerronContribution_eq_fourierIntegral
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) :
    smoothSaddleWideAnnularPerronContribution X y =
      (∫ t : ℝ, smoothSaddleWideAnnularFourierIntegrand X y t) /
        (Real.sqrt (2 * Real.pi) : ℂ) := by
  rw [smoothSaddleWideAnnularPerronContribution,
    integral_smoothSaddleWideAnnularFourierIntegrand_eq_intervalIntegrals hX hy,
    ← standardDeviation_mul_integral_perronLine_eq_wideAnnularIntervals hX hy]
  ring

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleWideAnnularPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleWideAnnularPerronContribution (X n) (y n))
      atTop (nhds 0) := by
  have h :=
    (hregime.tendsto_integral_smoothSaddleWideAnnularFourierIntegrand_zero hα).div_const
      (Real.sqrt (2 * Real.pi) : ℂ)
  have h' : Tendsto (fun n =>
      (∫ t : ℝ, smoothSaddleWideAnnularFourierIntegrand (X n) (y n) t) /
        (Real.sqrt (2 * Real.pi) : ℂ)) atTop (nhds 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  exact (smoothSaddleWideAnnularPerronContribution_eq_fourierIntegral
    hX hy).symm

end

end Tao2026
