import Tao2026.SmoothNumberSaddleHTMinorArcScale
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted integration of the HT minor arc

The finite-shell estimate which only uses `|kernel| <= 1` loses the full
length of a high-frequency interval.  On the physical Perron line the exact
Laplace kernel also has reciprocal-frequency decay.  This module records
that sharper bound as the input for integrating the unconditional HT
minor-arc estimate through its full finite height.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Interval

namespace Tao2026

noncomputable section

/-- Exact norm of the Laplace kernel after physical-frequency rescaling. -/
theorem norm_smoothSaddleLaplaceFourierKernel_physical
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) (t : ℝ) :
    ‖smoothSaddleLaplaceFourierKernel X y
        (-t * smoothSaddleStandardDeviation X y)‖ =
      smoothSaddlePoint X y /
        Real.sqrt (smoothSaddlePoint X y ^ 2 + t ^ 2) := by
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hsigma := smoothSaddlePoint_pos hX hy
  unfold smoothSaddleLaplaceFourierKernel smoothSaddleLaplaceRate
  have hq : -t * smoothSaddleStandardDeviation X y /
      (smoothSaddlePoint X y * smoothSaddleStandardDeviation X y) =
        -t / smoothSaddlePoint X y := by
    field_simp [hsd.ne', hsigma.ne']
  rw [hq, norm_div, norm_one]
  rw [show (1 : ℂ) - ((-t / smoothSaddlePoint X y : ℝ) : ℂ) *
      Complex.I = ((1 : ℝ) : ℂ) +
        ((t / smoothSaddlePoint X y : ℝ) : ℂ) * Complex.I by
      push_cast
      ring,
    Complex.norm_add_mul_I]
  have hsqrt : Real.sqrt
      (1 ^ 2 + (t / smoothSaddlePoint X y) ^ 2) =
      Real.sqrt (smoothSaddlePoint X y ^ 2 + t ^ 2) /
        smoothSaddlePoint X y := by
    have hins : 1 ^ 2 + (t / smoothSaddlePoint X y) ^ 2 =
        (smoothSaddlePoint X y ^ 2 + t ^ 2) /
          smoothSaddlePoint X y ^ 2 := by
      field_simp [hsigma.ne']
    rw [hins, Real.sqrt_div, Real.sqrt_sq_eq_abs, abs_of_pos hsigma]
    positivity
  rw [hsqrt]
  field_simp

/-- Away from frequency zero, the physical Laplace kernel retains the
reciprocal Perron weight. -/
theorem norm_smoothSaddleLaplaceFourierKernel_physical_le_div_abs
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {t : ℝ}
    (ht : 0 < |t|) :
    ‖smoothSaddleLaplaceFourierKernel X y
        (-t * smoothSaddleStandardDeviation X y)‖ ≤
      smoothSaddlePoint X y / |t| := by
  rw [norm_smoothSaddleLaplaceFourierKernel_physical hX hy]
  have hsigma := smoothSaddlePoint_pos hX hy
  have habsLe : |t| ≤
      Real.sqrt (smoothSaddlePoint X y ^ 2 + t ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs t]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (smoothSaddlePoint X y)])
  exact div_le_div_of_nonneg_left hsigma.le ht habsLe

/-- The HT characteristic estimate and the exact Laplace kernel give a
pointwise Perron bound which retains the reciprocal physical frequency. -/
theorem norm_smoothSaddlePerronLineIntegrand_le_hildebrandTenenbaum_div_abs
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {c lower upper t : ℝ}
    (hminor : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      X y c lower upper)
    (htLower : lower ≤ |t|) (htUpper : |t| ≤ upper)
    (ht : 0 < |t|) :
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
      Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t)) *
        (smoothSaddlePoint X y / |t|) := by
  rw [smoothSaddlePerronLineIntegrand_eq_characteristic_kernel hX hy,
    norm_mul]
  exact mul_le_mul (hminor t htLower htUpper)
    (norm_smoothSaddleLaplaceFourierKernel_physical_le_div_abs hX hy ht)
    (norm_nonneg _) (Real.exp_pos _).le

/-- On a positive interval, the reciprocal Perron weight has logarithmic
mass. -/
theorem integral_one_div_pos
    {lower upper : ℝ} (hlower : 0 < lower) (hlu : lower ≤ upper) :
    (∫ t in lower..upper, 1 / t) = Real.log (upper / lower) := by
  have hderiv : ∀ t ∈ Set.uIcc lower upper,
      HasDerivAt Real.log (1 / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    simpa [one_div] using Real.hasDerivAt_log
      (ne_of_gt (hlower.trans_le ht.1))
  have hcont : ContinuousOn (fun t : ℝ => 1 / t)
      (Set.uIcc lower upper) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    change t ≠ 0
    exact ne_of_gt (hlower.trans_le ht.1)
  calc
    (∫ t in lower..upper, 1 / t) =
        Real.log upper - Real.log lower := by
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        hderiv (hcont.intervalIntegrable :
          IntervalIntegrable (fun t : ℝ => 1 / t) volume lower upper)
    _ = Real.log (upper / lower) := by
      rw [Real.log_div (by linarith) (ne_of_gt hlower)]

/-- A reciprocal pointwise majorant costs only a logarithm on a positive
finite interval. -/
theorem norm_intervalIntegral_le_mul_log_of_norm_le_div
    {f : ℝ → ℂ} {A lower upper : ℝ}
    (hlower : 0 < lower) (hlu : lower ≤ upper)
    (hpoint : ∀ t ∈ Set.Icc lower upper, ‖f t‖ ≤ A / t) :
    ‖∫ t in lower..upper, f t‖ ≤
      A * Real.log (upper / lower) := by
  let g : ℝ → ℝ := fun t => A / t
  have hg : ContinuousOn g (Set.uIcc lower upper) := by
    dsimp [g]
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    rw [Set.uIcc_of_le hlu] at ht
    change t ≠ 0
    exact ne_of_gt (hlower.trans_le ht.1)
  have hraw := intervalIntegral.norm_integral_le_of_norm_le
    (f := f) (g := g) (a := lower) (b := upper) hlu (by
      filter_upwards with t ht
      have htIcc : t ∈ Set.Icc lower upper := by
        rw [Set.mem_Ioc] at ht
        exact ⟨ht.1.le, ht.2⟩
      exact hpoint t htIcc)
    (hg.intervalIntegrable : IntervalIntegrable g volume lower upper)
  calc
    ‖∫ t in lower..upper, f t‖ ≤ ∫ t in lower..upper, g t := hraw
    _ = A * (∫ t in lower..upper, 1 / t) := by
      dsimp [g]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _ht
      ring
    _ = A * Real.log (upper / lower) := by
      rw [integral_one_div_pos hlower hlu]

/-- Radial monotonicity freezes the HT exponential at the left endpoint
while preserving the reciprocal Perron weight. -/
theorem norm_smoothSaddlePerronLineIntegrand_le_ht_endpoint_div_abs
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {c lower upper t : ℝ} (hc : 0 ≤ c) (hlower : 0 < lower)
    (hminor : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      X y c lower upper)
    (htLower : lower ≤ |t|) (htUpper : |t| ≤ upper) :
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
      (Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y lower)) *
        smoothSaddlePoint X y) / |t| := by
  have ht : 0 < |t| := hlower.trans_le htLower
  have hraw :=
    norm_smoothSaddlePerronLineIntegrand_le_hildebrandTenenbaum_div_abs
      hX hy hminor htLower htUpper ht
  have hloss := smoothSaddleHildebrandTenenbaumLoss_mono
    hX hy hlower htLower
  rw [smoothSaddleHildebrandTenenbaumLoss_abs] at hloss
  have hexp : Real.exp (-(c *
      smoothSaddleHildebrandTenenbaumLoss X y t)) ≤
      Real.exp (-(c *
        smoothSaddleHildebrandTenenbaumLoss X y lower)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    ‖smoothSaddlePerronLineIntegrand X y t‖ ≤
        Real.exp (-(c * smoothSaddleHildebrandTenenbaumLoss X y t)) *
          (smoothSaddlePoint X y / |t|) := hraw
    _ ≤ Real.exp (-(c *
          smoothSaddleHildebrandTenenbaumLoss X y lower)) *
          (smoothSaddlePoint X y / |t|) := by
      exact mul_le_mul_of_nonneg_right hexp
        (div_nonneg (smoothSaddlePoint_pos hX hy).le (abs_nonneg t))
    _ = (Real.exp (-(c *
          smoothSaddleHildebrandTenenbaumLoss X y lower)) *
          smoothSaddlePoint X y) / |t| := by ring

/-- Weighted finite-shell integration of HT Lemma 8(ii). Unlike the coarse
finite-shell bound, the height cost is logarithmic. -/
theorem norm_smoothSaddleSymmetricPerronShellContribution_le_ht_log
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {c lower upper : ℝ} (hc : 0 ≤ c) (hlower : 0 < lower)
    (hlu : lower ≤ upper)
    (hminor : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      X y c lower upper) :
    ‖smoothSaddleSymmetricPerronShellContribution X y lower upper‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * (Real.exp (-(c *
            smoothSaddleHildebrandTenenbaumLoss X y lower)) *
          smoothSaddlePoint X y) * Real.log (upper / lower)) := by
  let f := smoothSaddlePerronLineIntegrand X y
  let A := Real.exp (-(c *
      smoothSaddleHildebrandTenenbaumLoss X y lower)) *
        smoothSaddlePoint X y
  have hright : ‖∫ t in lower..upper, f t‖ ≤
      A * Real.log (upper / lower) := by
    apply norm_intervalIntegral_le_mul_log_of_norm_le_div hlower hlu
    intro t ht
    have ht0 : 0 ≤ t := (hlower.le.trans ht.1)
    have hbound := norm_smoothSaddlePerronLineIntegrand_le_ht_endpoint_div_abs
      hX hy (t := t) hc hlower hminor
      (by simpa [abs_of_nonneg ht0] using ht.1)
      (by simpa [abs_of_nonneg ht0] using ht.2)
    simpa only [f, A, abs_of_nonneg ht0] using hbound
  have hleftIntegral : (∫ t in (-upper)..(-lower), f t) =
      ∫ t in lower..upper, f (-t) := by
    exact (intervalIntegral.integral_comp_neg
      (f := f) (a := lower) (b := upper)).symm
  have hleft : ‖∫ t in (-upper)..(-lower), f t‖ ≤
      A * Real.log (upper / lower) := by
    rw [hleftIntegral]
    apply norm_intervalIntegral_le_mul_log_of_norm_le_div hlower hlu
    intro t ht
    have ht0 : 0 ≤ t := hlower.le.trans ht.1
    have hbound := norm_smoothSaddlePerronLineIntegrand_le_ht_endpoint_div_abs
      hX hy hc hlower hminor
      (t := -t)
      (by simpa [abs_of_nonneg ht0] using ht.1)
      (by simpa [abs_of_nonneg ht0] using ht.2)
    simpa only [A, abs_neg, abs_of_nonneg ht0] using hbound
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  unfold smoothSaddleSymmetricPerronShellContribution
  change ‖((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-upper)..(-lower), f t) +
      ∫ t in lower..upper, f t)‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * A * Real.log (upper / lower))
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hsd.le, Real.norm_of_nonneg hsqrt.le]
  calc
    smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi) *
        ‖(∫ t in (-upper)..(-lower), f t) +
          ∫ t in lower..upper, f t‖ ≤
      smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi) *
        (‖∫ t in (-upper)..(-lower), f t‖ +
          ‖∫ t in lower..upper, f t‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi) *
        (2 * A * Real.log (upper / lower)) := by
      gcongr
      linarith

/-- A fixed fifth power is absorbed by the HT scale
`exp (-a*u/(log u)^2)`. -/
theorem tendsto_pow_five_mul_exp_neg_self_div_log_sq_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => u n ^ (5 : ℕ) *
      Real.exp (-a * (u n / Real.log (u n) ^ 2))) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (u n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hu
  have hupper : Tendsto (fun n =>
      (Real.sqrt (u n)) ^ (10 : ℝ) * Real.exp (-a * Real.sqrt (u n)))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 10 a ha).comp hsqrt
  have hlogSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 4)).def (by norm_num : (0 : ℝ) < 1)
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ u n ^ (5 : ℕ) *
      Real.exp (-a * (u n / Real.log (u n) ^ 2)) := by
    filter_upwards [hu.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    positivity
  refine squeeze_zero' hnonneg ?_ hupper
  filter_upwards [hu.eventually hlogSmall,
    hu.eventually (eventually_ge_atTop (2 : ℝ))] with n hlog huTwo
  have huPos : 0 < u n := by linarith
  have hlogPos : 0 < Real.log (u n) := Real.log_pos (by linarith)
  have hquarterPos : 0 < (u n) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos huPos _
  have hlogLe : Real.log (u n) ≤ (u n) ^ (1 / 4 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogPos,
      abs_of_pos hquarterPos, one_mul] using hlog
  have hlogSq : Real.log (u n) ^ 2 ≤ Real.sqrt (u n) := by
    calc
      Real.log (u n) ^ 2 ≤ ((u n) ^ (1 / 4 : ℝ)) ^ 2 := by
        nlinarith
      _ = Real.sqrt (u n) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul huPos.le,
          Real.sqrt_eq_rpow]
        norm_num
  have hsqrtPos : 0 < Real.sqrt (u n) := Real.sqrt_pos.2 huPos
  have hratio : Real.sqrt (u n) ≤ u n / Real.log (u n) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hlogPos)]
    calc
      Real.sqrt (u n) * Real.log (u n) ^ 2 ≤
          Real.sqrt (u n) * Real.sqrt (u n) :=
        mul_le_mul_of_nonneg_left hlogSq (Real.sqrt_nonneg _)
      _ = u n := Real.mul_self_sqrt huPos.le
  have hexp : Real.exp (-a * (u n / Real.log (u n) ^ 2)) ≤
      Real.exp (-a * Real.sqrt (u n)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hpow : (Real.sqrt (u n)) ^ (10 : ℝ) = u n ^ (5 : ℕ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul huPos.le]
    norm_num [Real.rpow_natCast]
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hexp (pow_nonneg huPos.le _)

theorem smoothSaddleHTFrequencyCeiling_half
    {y : ℕ} (hy : 1 ≤ y) :
    smoothSaddleHTFrequencyCeiling y (1 / 2) = (y : ℝ) := by
  unfold smoothSaddleHTFrequencyCeiling
  norm_num
  rw [Real.exp_log]
  positivity

/-- The explicit logarithmic envelope delivered by weighted HT integration
on the full source minor arc. -/
noncomputable def smoothSaddleHTMinorArcPerronEnvelope
    (X y : ℕ) : ℝ :=
  (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
    (2 * (Real.exp (-(smoothSaddleHTMinorArcCoefficient *
        smoothSaddleHildebrandTenenbaumLoss X y
          (1 / Real.log (y : ℝ)))) * smoothSaddlePoint X y) *
      Real.log (smoothSaddleHTFrequencyCeiling y (1 / 2) /
        (1 / Real.log (y : ℝ))))

/-- The weighted full-range HT envelope vanishes in every Tao-critical
smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTMinorArcPerronEnvelope_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTMinorArcPerronEnvelope (X n) (y n))
      atTop (𝓝 0) := by
  let c := smoothSaddleHTMinorArcCoefficient
  let a := c / 65
  let C := 4 * Real.sqrt 7 / Real.sqrt (2 * Real.pi)
  have hc : 0 < c := by
    dsimp [c]
    exact smoothSaddleHTMinorArcCoefficient_pos
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdecay := tendsto_pow_five_mul_exp_neg_self_div_log_sq_zero
    (hregime.tendsto_rankinRatio_atTop hα) ha
  have hupper : Tendsto (fun n => C *
      (smoothRankinRatio (X n) (y n) ^ (5 : ℕ) *
        Real.exp (-a * (smoothRankinRatio (X n) (y n) /
          Real.log (smoothRankinRatio (X n) (y n)) ^ 2))))
      atTop (𝓝 0) := by
    simpa using hdecay.const_mul C
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα,
      (hregime.tendsto_log_y_atTop hα).eventually
        (eventually_ge_atTop (1 : ℝ))] with n hX hy hL
    have hratio : 1 ≤ smoothSaddleHTFrequencyCeiling (y n) (1 / 2) /
        (1 / Real.log (y n : ℝ)) := by
      rw [smoothSaddleHTFrequencyCeiling_half (by omega : 1 ≤ y n)]
      have hyReal : (1 : ℝ) ≤ y n := by exact_mod_cast (show 1 ≤ y n by omega)
      rw [show (y n : ℝ) / (1 / Real.log (y n : ℝ)) =
        (y n : ℝ) * Real.log (y n : ℝ) by field_simp]
      nlinarith
    unfold smoothSaddleHTMinorArcPerronEnvelope
    apply mul_nonneg
    · exact div_nonneg (smoothSaddleStandardDeviation_pos hX hy).le
        (Real.sqrt_nonneg _)
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le
          (smoothSaddlePoint_pos hX hy).le))
        (Real.log_nonneg hratio)
  · have hlogRatio := hregime.tendsto_log_y_div_rankinRatio_sq_zero hα
    have hlogU : Tendsto
        (fun n => Real.log (smoothRankinRatio (X n) (y n))) atTop atTop :=
      Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
    filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα,
      (hregime.tendsto_log_y_atTop hα).eventually
        (eventually_ge_atTop (1 : ℝ)),
      hlogU.eventually (eventually_ge_atTop (1 : ℝ)),
      (hregime.tendsto_smoothSaddlePoint_one hα).eventually
        (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hregime.eventually_smoothSaddlePoint_lt_one hα,
      hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα,
      hlogRatio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hX hy hLone hvone hsigmaHalf hsigmaOne hdisp hLratio
    let u := smoothRankinRatio (X n) (y n)
    let L := Real.log (y n : ℝ)
    let v := Real.log u
    let sigma := smoothSaddlePoint (X n) (y n)
    let loss := smoothSaddleHildebrandTenenbaumLoss (X n) (y n) (1 / L)
    have hu : 0 < u := by dsimp [u]; exact smoothRankinRatio_pos hX hy
    have hL : 0 < L := by dsimp [L]; linarith
    have hv : 0 < v := by dsimp [v]; linarith
    have hsigmaPos : 0 < sigma := by dsimp [sigma]; exact smoothSaddlePoint_pos hX hy
    have hsigmaLe : sigma ≤ 1 := by dsimp [sigma]; exact hsigmaOne.le
    have hLle : L ≤ u ^ (2 : ℕ) := by
      have huSq : 0 < u ^ (2 : ℕ) := pow_pos hu _
      apply (div_lt_one huSq).mp at hLratio
      exact hLratio.le
    have hlogL : Real.log L ≤ L := by
      have := Real.log_le_sub_one_of_pos hL
      linarith
    have hheightLog : Real.log
        (smoothSaddleHTFrequencyCeiling (y n) (1 / 2) / (1 / L)) ≤
          2 * L := by
      rw [smoothSaddleHTFrequencyCeiling_half (by omega : 1 ≤ y n)]
      have hyPos : 0 < (y n : ℝ) := by positivity
      rw [show (y n : ℝ) / (1 / L) = (y n : ℝ) * L by
        field_simp]
      rw [Real.log_mul hyPos.ne' hL.ne']
      dsimp [L]
      linarith
    have hloss : u / (65 * v ^ 2) ≤ loss := by
      exact smoothRankinRatio_div_log_sq_le_smoothSaddleHTLoss_firstOuter
        hX hy hL (by simpa only [v] using hvone) hsigmaOne.le hdisp.le
    have hexp : Real.exp (-(c * loss)) ≤
        Real.exp (-a * (u / v ^ 2)) := by
      have := mul_le_mul_of_nonneg_left hloss hc.le
      have heq : a * (u / v ^ 2) = c * (u / (65 * v ^ 2)) := by
        dsimp [a]
        ring
      apply Real.exp_le_exp.mpr
      calc
        -(c * loss) ≤ -(c * (u / (65 * v ^ 2))) := neg_le_neg this
        _ = -(a * (u / v ^ 2)) := congrArg Neg.neg heq.symm
        _ = -a * (u / v ^ 2) := by ring
    have hsdDiv := smoothSaddleStandardDeviation_div_log_le_sqrt_rankinRatio
      hX hy hsigmaHalf.le
    have hsd : smoothSaddleStandardDeviation (X n) (y n) ≤
        L * Real.sqrt (7 * u) := by
      have hsd' := (div_le_iff₀ hL).mp
        (by simpa only [L, u] using hsdDiv)
      nlinarith
    have hsqrtMul : Real.sqrt (7 * u) = Real.sqrt 7 * Real.sqrt u := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7)]
    have huOne : 1 ≤ u := by
      have hv0 : 0 ≤ Real.log u := by
        have : 1 ≤ Real.log u := by simpa only [v] using hvone
        linarith
      have he := Real.exp_le_exp.mpr hv0
      rw [Real.exp_zero, Real.exp_log hu] at he
      exact he
    have hsqrtU : Real.sqrt u ≤ u := by
      nlinarith [Real.sq_sqrt hu.le, Real.sqrt_nonneg u]
    have hheightLogNonneg : 0 ≤ Real.log
        (smoothSaddleHTFrequencyCeiling (y n) (1 / 2) / (1 / L)) := by
      apply Real.log_nonneg
      rw [smoothSaddleHTFrequencyCeiling_half (by omega : 1 ≤ y n)]
      rw [show (y n : ℝ) / (1 / L) = (y n : ℝ) * L by field_simp]
      have hyReal : (1 : ℝ) ≤ y n := by exact_mod_cast (show 1 ≤ y n by omega)
      nlinarith
    unfold smoothSaddleHTMinorArcPerronEnvelope
    change (smoothSaddleStandardDeviation (X n) (y n) /
        Real.sqrt (2 * Real.pi)) *
      (2 * (Real.exp (-(c * loss)) * sigma) *
        Real.log (smoothSaddleHTFrequencyCeiling (y n) (1 / 2) /
          (1 / L))) ≤
      C * (u ^ (5 : ℕ) * Real.exp (-a * (u / v ^ 2)))
    calc
      (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
        (2 * (Real.exp (-(c * loss)) * sigma) *
          Real.log (smoothSaddleHTFrequencyCeiling (y n) (1 / 2) /
            (1 / L))) ≤
        (L * Real.sqrt (7 * u) / Real.sqrt (2 * Real.pi)) *
          (2 * (Real.exp (-a * (u / v ^ 2)) * 1) * (2 * L)) := by
        gcongr
      _ = C * (L ^ 2 * Real.sqrt u *
          Real.exp (-a * (u / v ^ 2))) := by
        rw [hsqrtMul]
        dsimp [C]
        ring
      _ ≤ C * (u ^ (5 : ℕ) * Real.exp (-a * (u / v ^ 2))) := by
        gcongr
        calc
          L ^ 2 * Real.sqrt u ≤ (u ^ (2 : ℕ)) ^ 2 * Real.sqrt u := by
            gcongr
          _ ≤ u ^ (5 : ℕ) := by
            nlinarith [hsqrtU, hu]

/-- The complete finite symmetric Perron contribution on the HT minor arc. -/
noncomputable def smoothSaddleHTMinorArcPerronContribution
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (1 / Real.log (y : ℝ))
    (smoothSaddleHTFrequencyCeiling y (1 / 2))

/-- The unconditional HT minor arc has vanishing normalized Perron mass in
every Tao-critical smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTMinorArcPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTMinorArcPerronContribution (X n) (y n))
      atTop (𝓝 0) := by
  have henvelope :=
    hregime.tendsto_smoothSaddleHTMinorArcPerronEnvelope_zero hα
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    henvelope
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hregime.eventually_smoothSaddleHTMinorArcBoundAt hα] with
      n hX hy hlogY hminor
  have hlogPos : 0 < Real.log (y n : ℝ) := by linarith
  have hlower : 0 < 1 / Real.log (y n : ℝ) := one_div_pos.mpr hlogPos
  have hlu : 1 / Real.log (y n : ℝ) ≤
      smoothSaddleHTFrequencyCeiling (y n) (1 / 2) := by
    rw [smoothSaddleHTFrequencyCeiling_half (by omega : 1 ≤ y n)]
    have hone : 1 / Real.log (y n : ℝ) ≤ 1 :=
      (div_le_one hlogPos).2 hlogY
    exact hone.trans (by exact_mod_cast (show 1 ≤ y n by omega))
  unfold smoothSaddleHTMinorArcPerronContribution
  exact norm_smoothSaddleSymmetricPerronShellContribution_le_ht_log
    hX hy smoothSaddleHTMinorArcCoefficient_pos.le hlower hlu hminor

noncomputable def smoothSaddleHTInitialOverlapPerronContribution
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (1 / Real.log (y : ℝ)) (smoothSaddleWidePerronHeight X y)

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTInitialOverlapPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTInitialOverlapPerronContribution
      (X n) (y n)) atTop (𝓝 0) := by
  have henvelope :=
    hregime.tendsto_smoothSaddleHTMinorArcPerronEnvelope_zero hα
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    henvelope
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_y_atTop hα).eventually (eventually_ge_atTop 4),
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hregime.eventually_smoothSaddleHTMinorArcBoundAt hα] with
      n hX hy hyFour hlogY hminor
  let lower := 1 / Real.log (y n : ℝ)
  let middle := smoothSaddleWidePerronHeight (X n) (y n)
  let upper := smoothSaddleHTFrequencyCeiling (y n) (1 / 2)
  have hlogPos : 0 < Real.log (y n : ℝ) := by linarith
  have hlower : 0 < lower := by dsimp [lower]; positivity
  have hlm : lower ≤ middle := by
    dsimp [lower, middle]
    rw [smoothSaddleWidePerronHeight_eq_pi_div_log hX hy]
    exact div_le_div_of_nonneg_right (by linarith [Real.pi_gt_three]) hlogPos.le
  have hmu : middle ≤ upper := by
    dsimp [middle, upper]
    rw [smoothSaddleWidePerronHeight_eq_pi_div_log hX hy,
      smoothSaddleHTFrequencyCeiling_half (by omega : 1 ≤ y n)]
    have hpiDiv : Real.pi / Real.log (y n : ℝ) ≤ Real.pi := by
      exact div_le_self Real.pi_pos.le hlogY
    have hpiY : Real.pi ≤ (y n : ℝ) := by
      have : (4 : ℝ) ≤ y n := by exact_mod_cast hyFour
      linarith [Real.pi_lt_four]
    exact hpiDiv.trans hpiY
  have hminorInitial : SmoothSaddleHildebrandTenenbaumMinorArcBoundAt
      (X n) (y n) smoothSaddleHTMinorArcCoefficient lower middle := by
    intro t htLower htUpper
    exact hminor t htLower (htUpper.trans hmu)
  have hnorm := norm_smoothSaddleSymmetricPerronShellContribution_le_ht_log
    hX hy smoothSaddleHTMinorArcCoefficient_pos.le hlower hlm hminorInitial
  have hlogMono : Real.log (middle / lower) ≤ Real.log (upper / lower) := by
    apply Real.log_le_log
    · exact div_pos (hlower.trans_le hlm) hlower
    · exact div_le_div_of_nonneg_right hmu hlower.le
  unfold smoothSaddleHTInitialOverlapPerronContribution
  calc
    ‖smoothSaddleSymmetricPerronShellContribution (X n) (y n)
        lower middle‖ ≤
      (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
        (2 * (Real.exp (-(smoothSaddleHTMinorArcCoefficient *
            smoothSaddleHildebrandTenenbaumLoss (X n) (y n) lower)) *
          smoothSaddlePoint (X n) (y n)) * Real.log (middle / lower)) := hnorm
    _ ≤ smoothSaddleHTMinorArcPerronEnvelope (X n) (y n) := by
      unfold smoothSaddleHTMinorArcPerronEnvelope
      dsimp [lower, upper]
      have hP : 0 ≤ smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi) := by
        exact div_nonneg (smoothSaddleStandardDeviation_pos hX hy).le
          (Real.sqrt_nonneg _)
      have hB : 0 ≤ 2 *
          (Real.exp (-(smoothSaddleHTMinorArcCoefficient *
              smoothSaddleHildebrandTenenbaumLoss (X n) (y n)
                (1 / Real.log (y n : ℝ)))) *
            smoothSaddlePoint (X n) (y n)) := by
        exact mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le
          (smoothSaddlePoint_pos hX hy).le)
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogMono hB) hP

/-- The exact finite outer segment from the established wide Perron height
to the HT source ceiling. -/
noncomputable def smoothSaddleHTOuterPerronContribution
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleWidePerronHeight X y)
    (smoothSaddleHTFrequencyCeiling y (1 / 2))

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTOuterPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTOuterPerronContribution (X n) (y n))
      atTop (𝓝 0) := by
  have hdiff :=
    (hregime.tendsto_smoothSaddleHTMinorArcPerronContribution_zero hα).sub
      (hregime.tendsto_smoothSaddleHTInitialOverlapPerronContribution_zero hα)
  have hdiff' : Tendsto (fun n =>
      smoothSaddleHTMinorArcPerronContribution (X n) (y n) -
        smoothSaddleHTInitialOverlapPerronContribution (X n) (y n))
      atTop (𝓝 0) := by simpa using hdiff
  apply hdiff'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  unfold smoothSaddleHTMinorArcPerronContribution
    smoothSaddleHTInitialOverlapPerronContribution
    smoothSaddleHTOuterPerronContribution
  have hadd := smoothSaddleSymmetricPerronShellContribution_add_adjacent
    hX hy (1 / Real.log (y n : ℝ))
      (smoothSaddleWidePerronHeight (X n) (y n))
      (smoothSaddleHTFrequencyCeiling (y n) (1 / 2))
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hadd.symm

end

end Tao2026
