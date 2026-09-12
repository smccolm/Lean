import Tao2026.BadIntervalSourceScales
import Tao2026.SmoothNumberPrimeSum

/-!
# Source regimes for Tao's smooth-number estimate

This module gives a precise logarithmic-ratio meaning to the critical source
regime `X = x^(1+o(1))`, `y = z(x)^(α+o(1))`, with `α` fixed before
`x → ∞`.  It connects that contract to the finite Rankin estimates.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- Exact filter-based encoding of Tao's critical smooth-number regime.
The first convergence says `X = x^(1+o(1))`; the second says
`y = z(x)^(α+o(1))`. -/
def IsTaoCriticalSmoothRegime
    (X y : ℕ → ℕ) (α : ℝ) : Prop :=
  Tendsto (fun x => Real.log (X x) / Real.log x) atTop (𝓝 1) ∧
    Tendsto (fun x => Real.log (y x) / Real.log (taoZ x)) atTop (𝓝 α)

/-- In the critical source regime, the Rankin ratio normalized by Tao's
`u₀` tends to `1/α`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_div_taoUZero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => smoothRankinRatio (X x) (y x) / taoUZero x)
      atTop (𝓝 (1 / α)) := by
  have hratio := hregime.1.div hregime.2 hα.ne'
  apply hratio.congr'
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyRatioPos : ∀ᶠ x in atTop,
      0 < Real.log (y x) / Real.log (taoZ x) :=
    hregime.2.eventually (Ioi_mem_nhds hα)
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    hyRatioPos] with x hlogPos hiterPos hzOne hyRatioPos'
  have hzLogPos : 0 < Real.log (taoZ x) := Real.log_pos hzOne
  have hyLogNe : Real.log (y x) ≠ 0 := by
    intro hyZero
    rw [hyZero, zero_div] at hyRatioPos'
    linarith
  change
    (Real.log (X x) / Real.log x) /
        (Real.log (y x) / Real.log (taoZ x)) =
      smoothRankinRatio (X x) (y x) / taoUZero x
  rw [← log_div_log_taoZ_eq_taoUZero hlogPos hiterPos]
  unfold smoothRankinRatio
  field_simp [hlogPos.ne', hzLogPos.ne', hyLogNe]

/-- Consequently the Rankin ratio itself tends to infinity throughout every
critical source regime with fixed positive `α`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => smoothRankinRatio (X x) (y x)) atTop atTop := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoUZero hα
  have hproduct := hnormalized.pos_mul_atTop (one_div_pos.mpr hα)
    tendsto_taoUZero_atTop
  apply hproduct.congr'
  filter_upwards [tendsto_taoUZero_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x huPos
  field_simp [huPos.ne']

/-- In the critical regime, the logarithmic smoothness scale is negligible
compared with the square of the Rankin ratio. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_y_div_rankinRatio_sq_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (y x) /
      smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoUZero hα
  have hnormalizedSq := hnormalized.pow 2
  have hlimitNe : (1 / α) ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero _ (one_div_ne_zero hα.ne')
  have hboundedRatio := hregime.2.div hnormalizedSq hlimitNe
  have hproduct := hboundedRatio.mul tendsto_log_taoZ_div_taoUZero_sq_zero
  have hproductZero : Tendsto (fun x =>
      (Real.log (y x) / Real.log (taoZ x) /
          (smoothRankinRatio (X x) (y x) / taoUZero x) ^ (2 : ℕ)) *
        (Real.log (taoZ x) / taoUZero x ^ (2 : ℕ))) atTop (𝓝 0) := by
    simpa using hproduct
  apply hproductZero.congr'
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hyRatioPos : ∀ᶠ x in atTop,
      0 < Real.log (y x) / Real.log (taoZ x) :=
    hregime.2.eventually (Ioi_mem_nhds hα)
  filter_upwards [tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_taoUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    huTop.eventually (eventually_gt_atTop (0 : ℝ)), hyRatioPos] with
      x hzOne huZeroPos huPos hyRatioPos'
  have hzLogPos : 0 < Real.log (taoZ x) := Real.log_pos hzOne
  have hyLogNe : Real.log (y x) ≠ 0 := by
    intro hyZero
    rw [hyZero, zero_div] at hyRatioPos'
    linarith
  field_simp [hzLogPos.ne', huZeroPos.ne', huPos.ne', hyLogNe]

/-- The harmless factor `2` in the dyadic terminal scale does not affect the
critical logarithmic decay. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_two_mul_y_div_rankinRatio_sq_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (2 * (y x : ℝ)) /
      smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) := by
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have huSqTop : Tendsto
      (fun x => smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop atTop := by
    simpa [pow_two] using huTop.atTop_mul_atTop₀ huTop
  have hconst : Tendsto (fun x => Real.log 2 /
      smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop huSqTop
  have hsum := hconst.add (hregime.tendsto_log_y_div_rankinRatio_sq_zero hα)
  have hsumZero : Tendsto (fun x =>
      Real.log 2 / smoothRankinRatio (X x) (y x) ^ (2 : ℕ) +
        Real.log (y x) / smoothRankinRatio (X x) (y x) ^ (2 : ℕ))
      atTop (𝓝 0) := by
    simpa using hsum
  apply hsumZero.congr'
  have hyTop : Tendsto (fun x => Real.log (y x)) atTop atTop := by
    have hproduct := hregime.2.pos_mul_atTop hα
      (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop)
    apply hproduct.congr'
    filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with x hzOne
    have hzLogNe : Real.log (taoZ x) ≠ 0 := (Real.log_pos hzOne).ne'
    simp only [Function.comp_apply]
    field_simp [hzLogNe]
  filter_upwards [hyTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hyLogPos
  have hyPos : (0 : ℝ) < y x := by
    have hyOne : (1 : ℝ) < y x :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hyLogPos
    linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne']
  ring

/-- The exact quadratic dyadic-depth envelope required by the generic scalar
consumer holds eventually throughout the critical source regime. -/
theorem IsTaoCriticalSmoothRegime.eventually_logScale_le_rankinRatio_sq
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop,
      Real.log (2 * (y x : ℝ)) / Real.log 2 ≤
        smoothRankinRatio (X x) (y x) ^ (2 : ℕ) := by
  have hdecay : Tendsto (fun x =>
      (Real.log (2 * (y x : ℝ)) / Real.log 2) /
        smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) := by
    have h := (hregime.tendsto_log_two_mul_y_div_rankinRatio_sq_zero hα).const_mul
      (1 / Real.log 2)
    have hzero : Tendsto (fun x =>
        1 / Real.log 2 *
          (Real.log (2 * (y x : ℝ)) /
            smoothRankinRatio (X x) (y x) ^ (2 : ℕ))) atTop (𝓝 0) := by
      simpa using h
    apply hzero.congr'
    filter_upwards with x
    ring
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  filter_upwards [hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    huTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx huPos
  rw [div_lt_iff₀ (sq_pos_of_pos huPos)] at hx
  simpa only [one_mul] using hx.le

/-- The logarithm of the ambient cutoff tends to infinity in every critical
source regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_X_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) :
    Tendsto (fun x => Real.log (X x)) atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hproduct := hregime.1.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hlog
  apply hproduct.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp [hx.ne']

/-- The logarithm of the smoothness cutoff tends to infinity when the fixed
critical exponent is positive. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_y_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (y x)) atTop atTop := by
  have hproduct := hregime.2.pos_mul_atTop hα
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop)
  apply hproduct.congr'
  filter_upwards [tendsto_taoZ_atTop.eventually
    (eventually_gt_atTop (1 : ℝ))] with x hzOne
  have hzLogNe : Real.log (taoZ x) ≠ 0 := (Real.log_pos hzOne).ne'
  simp only [Function.comp_apply]
  field_simp [hzLogNe]

theorem IsTaoCriticalSmoothRegime.eventually_two_le_X
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) :
    ∀ᶠ x in atTop, 2 ≤ X x := by
  filter_upwards [hregime.tendsto_log_X_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  have hone : (1 : ℝ) < X x :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hx
  exact_mod_cast hone

theorem IsTaoCriticalSmoothRegime.eventually_two_le_y
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop, 2 ≤ y x := by
  filter_upwards [hregime.tendsto_log_y_atTop hα |>.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  have hone : (1 : ℝ) < y x :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hx
  exact_mod_cast hone

theorem IsTaoCriticalSmoothRegime.eventually_one_lt_rankinRatio
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop, 1 < smoothRankinRatio (X x) (y x) :=
  (hregime.tendsto_rankinRatio_atTop hα).eventually (eventually_gt_atTop 1)

/-- The critical smoothness cutoff grows faster than its Rankin ratio.  This
is the source-scale comparison which places the standard saddle at a
nonnegative parameter. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_lt_y
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop, smoothRankinRatio (X x) (y x) < y x := by
  let b : ℝ := α / (2 * Real.sqrt 2)
  let K : ℝ := 2 / α
  let C : ℝ := K * Real.sqrt 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := mul_pos hK (Real.sqrt_pos.2 (by norm_num))
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsqrtLog : Tendsto (fun x : ℕ => Real.sqrt (Real.log x))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hlog
  have hdom : ∀ᶠ x : ℕ in atTop,
      C < Real.exp (b * Real.sqrt (Real.log x)) /
        Real.sqrt (Real.log x) ^ (1 : ℝ) :=
    ((tendsto_exp_mul_div_rpow_atTop (1 : ℝ) b hb).comp hsqrtLog).eventually
      (eventually_gt_atTop C)
  have hnormalizedUpper : ∀ᶠ x in atTop,
      smoothRankinRatio (X x) (y x) / taoUZero x < K := by
    have hlimit : 1 / α < K := by
      dsimp [K]
      exact (div_lt_div_iff_of_pos_right hα).2 (by norm_num)
    exact (hregime.tendsto_rankinRatio_div_taoUZero hα).eventually
      (Iio_mem_nhds hlimit)
  have hyRatioLower : ∀ᶠ x in atTop,
      α / 2 < Real.log (y x) / Real.log (taoZ x) := by
    have hhalf : α / 2 < α := by linarith
    exact hregime.2.eventually (Ioi_mem_nhds hhalf)
  filter_upwards [hdom, hnormalizedUpper, hyRatioLower,
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_taoUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hxDom hxNorm hyRatio hlogPos hiterOne huZeroPos hzOne
  have hsqrtLogPos : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.2 hlogPos
  have hsqrtIterPos : 0 < Real.sqrt (iteratedLog x) := by
    have : (0 : ℝ) < iteratedLog x := lt_of_lt_of_le zero_lt_one hiterOne
    exact Real.sqrt_pos.2 this
  have hsqrtIterOne : 1 ≤ Real.sqrt (iteratedLog x) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ iteratedLog x by positivity),
      Real.sqrt_nonneg (iteratedLog x)]
  have huZeroBound : taoUZero x ≤ Real.sqrt 2 * Real.sqrt (Real.log x) := by
    rw [taoUZero, div_le_iff₀ hsqrtIterPos]
    exact le_mul_of_one_le_right (by positivity) hsqrtIterOne
  have huBound : smoothRankinRatio (X x) (y x) <
      C * Real.sqrt (Real.log x) := by
    have huK : smoothRankinRatio (X x) (y x) < K * taoUZero x :=
      (div_lt_iff₀ huZeroPos).mp hxNorm
    calc
      smoothRankinRatio (X x) (y x) < K * taoUZero x := huK
      _ ≤ K * (Real.sqrt 2 * Real.sqrt (Real.log x)) :=
        mul_le_mul_of_nonneg_left huZeroBound hK.le
      _ = C * Real.sqrt (Real.log x) := by simp [C, mul_assoc]
  have hCexp : C * Real.sqrt (Real.log x) <
      Real.exp (b * Real.sqrt (Real.log x)) := by
    rw [Real.rpow_one] at hxDom
    exact (lt_div_iff₀ hsqrtLogPos).mp hxDom
  have hzLogPos : 0 < Real.log (taoZ x) := Real.log_pos hzOne
  have hzLower :
      (1 / Real.sqrt 2) * Real.sqrt (Real.log x) ≤
        Real.log (taoZ x) := by
    rw [log_taoZ]
    exact le_mul_of_one_le_right (by positivity) hsqrtIterOne
  have hbLower : b * Real.sqrt (Real.log x) ≤
      (α / 2) * Real.log (taoZ x) := by
    calc
      b * Real.sqrt (Real.log x) =
          (α / 2) * ((1 / Real.sqrt 2) * Real.sqrt (Real.log x)) := by
            simp [b]
            ring
      _ ≤ (α / 2) * Real.log (taoZ x) :=
        mul_le_mul_of_nonneg_left hzLower (by positivity)
  have hyLogLower : (α / 2) * Real.log (taoZ x) < Real.log (y x) :=
    (lt_div_iff₀ hzLogPos).mp hyRatio
  have hyLogPos : 0 < Real.log (y x) :=
    lt_of_le_of_lt (mul_nonneg (by positivity) hzLogPos.le) hyLogLower
  have hyPos : (0 : ℝ) < y x := by
    have : (1 : ℝ) < y x :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hyLogPos
    linarith
  calc
    smoothRankinRatio (X x) (y x) <
        C * Real.sqrt (Real.log x) := huBound
    _ < Real.exp (b * Real.sqrt (Real.log x)) := hCexp
    _ ≤ Real.exp (Real.log (y x)) := Real.exp_le_exp.mpr (hbLower.trans hyLogLower.le)
    _ = (y x : ℝ) := Real.exp_log hyPos

theorem IsTaoCriticalSmoothRegime.eventually_smoothRankinSigma_nonneg
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop, 0 ≤ smoothRankinSigma (X x) (y x) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_rankinRatio_lt_y hα] with x hX hy huY
  exact (smoothRankinSigma_pos hX hy huY).le

theorem IsTaoCriticalSmoothRegime.eventually_smoothRankinSigma_pos
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop, 0 < smoothRankinSigma (X x) (y x) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_rankinRatio_lt_y hα] with x hX hy huY
  exact smoothRankinSigma_pos hX hy huY

/-- The logarithm of the critical Rankin ratio is negligible on the `log z`
scale. -/
theorem IsTaoCriticalSmoothRegime.tendsto_log_rankinRatio_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => Real.log (smoothRankinRatio (X x) (y x)) /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoUZero hα
  have hlogNormalized : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoUZero x))
      atTop (𝓝 (Real.log (1 / α))) :=
    (Real.continuousAt_log (one_div_ne_zero hα.ne')).tendsto.comp hnormalized
  have hlogZ : Tendsto (fun x : ℕ => Real.log (taoZ x)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_taoZ_atTop
  have hnormalizedZero := hlogNormalized.div_atTop hlogZ
  have hsum := hnormalizedZero.add tendsto_log_taoUZero_div_log_taoZ_zero
  have hsumZero : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoUZero x) /
          Real.log (taoZ x) +
        Real.log (taoUZero x) / Real.log (taoZ x)) atTop (𝓝 0) := by
    simpa using hsum
  apply hsumZero.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds (one_div_pos.mpr hα)),
    tendsto_taoUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hnormPos huZeroPos hzOne
  have hproduct :
      (smoothRankinRatio (X x) (y x) / taoUZero x) * taoUZero x =
        smoothRankinRatio (X x) (y x) := by
    field_simp [huZeroPos.ne']
  have hlogProduct :
      Real.log (smoothRankinRatio (X x) (y x)) =
        Real.log (smoothRankinRatio (X x) (y x) / taoUZero x) +
          Real.log (taoUZero x) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' huZeroPos.ne']
  rw [hlogProduct]
  ring

/-- The standard saddle parameter tends to one in the critical source
regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothRankinSigma_one
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => smoothRankinSigma (X x) (y x)) atTop (𝓝 1) := by
  have hquotient :=
    (hregime.tendsto_log_rankinRatio_div_log_taoZ_zero hα).div
      hregime.2 hα.ne'
  have hzero : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x)) / Real.log (y x))
      atTop (𝓝 0) := by
    have hquotientZero : Tendsto
        ((fun x => Real.log (smoothRankinRatio (X x) (y x)) /
            Real.log (taoZ x)) /
          (fun x => Real.log (y x) / Real.log (taoZ x)))
        atTop (𝓝 0) := by
      simpa using hquotient
    apply hquotientZero.congr'
    filter_upwards [tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      hregime.tendsto_log_y_atTop hα |>.eventually
        (eventually_gt_atTop (0 : ℝ))] with x hzOne hyLogPos
    change
      (Real.log (smoothRankinRatio (X x) (y x)) / Real.log (taoZ x)) /
          (Real.log (y x) / Real.log (taoZ x)) =
        Real.log (smoothRankinRatio (X x) (y x)) / Real.log (y x)
    field_simp [(Real.log_pos hzOne).ne', hyLogPos.ne']
  have h : Tendsto (fun x =>
      1 - Real.log (smoothRankinRatio (X x) (y x)) / Real.log (y x))
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hzero
  simpa [smoothRankinSigma] using h

/-- The Rankin ratio itself is negligible compared with `log z`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => smoothRankinRatio (X x) (y x) /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hproduct := (hregime.tendsto_rankinRatio_div_taoUZero hα).mul
    tendsto_taoUZero_div_log_taoZ_zero
  have hzero : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) / taoUZero x) *
        (taoUZero x / Real.log (taoZ x))) atTop (𝓝 0) := by
    simpa using hproduct
  apply hzero.congr'
  filter_upwards [tendsto_taoUZero_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x huZeroPos
  field_simp [huZeroPos.ne']

/-- The exact leading Rankin saving in a critical source regime is
`(1/α) log z`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_mul_log_div_log_taoZ
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x =>
      smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) /
        Real.log (taoZ x)) atTop (𝓝 (1 / α)) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoUZero hα
  have hlogNormalized : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoUZero x))
      atTop (𝓝 (Real.log (1 / α))) :=
    (Real.continuousAt_log (one_div_ne_zero hα.ne')).tendsto.comp hnormalized
  have hcorrection := tendsto_taoUZero_div_log_taoZ_zero.mul hlogNormalized
  have hsourceWithCorrection :=
    tendsto_taoUZero_mul_log_div_log_taoZ_one.add hcorrection
  have hsourceOne : Tendsto (fun x =>
      taoUZero x * Real.log (taoUZero x) / Real.log (taoZ x) +
        (taoUZero x / Real.log (taoZ x)) *
          Real.log (smoothRankinRatio (X x) (y x) / taoUZero x))
      atTop (𝓝 1) := by
    simpa using hsourceWithCorrection
  have hproduct := hnormalized.mul hsourceOne
  have hlimit : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) / taoUZero x) *
        (taoUZero x * Real.log (taoUZero x) / Real.log (taoZ x) +
          (taoUZero x / Real.log (taoZ x)) *
            Real.log (smoothRankinRatio (X x) (y x) / taoUZero x)))
      atTop (𝓝 (1 / α)) := by
    simpa using hproduct
  apply hlimit.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds (one_div_pos.mpr hα)),
    tendsto_taoUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hnormPos huZeroPos hzOne
  have hproductEq :
      (smoothRankinRatio (X x) (y x) / taoUZero x) * taoUZero x =
        smoothRankinRatio (X x) (y x) := by
    field_simp [huZeroPos.ne']
  have hlogProduct :
      Real.log (smoothRankinRatio (X x) (y x)) =
        Real.log (smoothRankinRatio (X x) (y x) / taoUZero x) +
          Real.log (taoUZero x) := by
    conv_lhs => rw [← hproductEq]
    rw [Real.log_mul hnormPos.ne' huZeroPos.ne']
  rw [hlogProduct]
  field_simp [huZeroPos.ne', (Real.log_pos hzOne).ne']
  ring

/-- The complete positive error in the compressed dyadic Rankin bound is
negligible compared with `log z`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothDyadicSaddleError_div_log_taoZ_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x => smoothDyadicSaddleError (X x) (y x) /
      Real.log (taoZ x)) atTop (𝓝 0) := by
  have hsigma := hregime.tendsto_smoothRankinSigma_one hα
  have hnegSigma := hsigma.neg
  have hrpow : Tendsto (fun x =>
      (2 : ℝ) ^ (-smoothRankinSigma (X x) (y x)))
      atTop (𝓝 ((2 : ℝ) ^ (-1 : ℝ))) :=
    (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
      hnegSigma
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hdenominator := hone.sub hrpow
  have hfactorRaw := hdenominator.inv₀ (by norm_num :
    (1 - (2 : ℝ) ^ (-1 : ℝ)) ≠ 0)
  have hfactor : Tendsto (fun x =>
      (1 - (2 : ℝ) ^ (-smoothRankinSigma (X x) (y x)))⁻¹)
      atTop (𝓝 2) := by
    convert hfactorRaw using 1
    all_goals norm_num [Real.rpow_neg_one]
  have huZ := hregime.tendsto_rankinRatio_div_log_taoZ_zero hα
  have hyLogTop := hregime.tendsto_log_y_atTop hα
  have huLogTop : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
  have hyInv := hyLogTop.inv_tendsto_atTop
  have huInv := huLogTop.inv_tendsto_atTop
  have hAraw :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => smoothPrimeCountingConstant)
      atTop (𝓝 smoothPrimeCountingConstant)).mul huZ |>.mul hyInv
  have hArawZero : Tendsto
      (fun x => smoothPrimeCountingConstant *
        (smoothRankinRatio (X x) (y x) / Real.log (taoZ x)) *
          (Real.log (y x))⁻¹) atTop (𝓝 0) := by
    simpa using hAraw
  have hA : Tendsto
      (fun x => (smoothPrimeCountingConstant *
        smoothRankinRatio (X x) (y x) / Real.log (y x)) /
          Real.log (taoZ x)) atTop (𝓝 0) := by
    apply hArawZero.congr'
    filter_upwards [tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      hyLogTop.eventually (eventually_gt_atTop (0 : ℝ))] with
        x hzOne hyLogPos
    field_simp [(Real.log_pos hzOne).ne', hyLogPos.ne']
  let D : ℝ := 5 * smoothPrimeCountingConstant / Real.log 2
  have hDraw : Tendsto (fun _ : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
  have hBraw := ((hDraw.mul hsigma).mul huZ).mul huInv
  have hBrawZero : Tendsto
      (fun x => D * smoothRankinSigma (X x) (y x) *
        (smoothRankinRatio (X x) (y x) / Real.log (taoZ x)) *
          (Real.log (smoothRankinRatio (X x) (y x)))⁻¹)
      atTop (𝓝 0) := by
    simpa using hBraw
  have hB : Tendsto
      (fun x => (smoothPrimeCountingConstant *
        smoothRankinSigma (X x) (y x) *
          ((5 * smoothRankinRatio (X x) (y x) /
            Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
          Real.log (taoZ x)) atTop (𝓝 0) := by
    apply hBrawZero.congr'
    filter_upwards [tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
      huLogTop.eventually (eventually_gt_atTop (0 : ℝ))] with
        x hzOne huLogPos
    dsimp only [D]
    field_simp [(Real.log_pos hzOne).ne', huLogPos.ne',
      (Real.log_pos one_lt_two).ne']
  have hinsideSum : Tendsto
      (fun x =>
        (smoothPrimeCountingConstant * smoothRankinRatio (X x) (y x) /
          Real.log (y x)) / Real.log (taoZ x) +
        (smoothPrimeCountingConstant * smoothRankinSigma (X x) (y x) *
          ((5 * smoothRankinRatio (X x) (y x) /
            Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
          Real.log (taoZ x))
      atTop (𝓝 0) := by
    simpa using hA.add hB
  have hinside : Tendsto
      (fun x =>
        (smoothPrimeCountingConstant * smoothRankinRatio (X x) (y x) /
            Real.log (y x) +
          smoothPrimeCountingConstant * smoothRankinSigma (X x) (y x) *
            ((5 * smoothRankinRatio (X x) (y x) /
              Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
          Real.log (taoZ x))
      atTop (𝓝 0) := by
    apply hinsideSum.congr'
    filter_upwards with x
    ring
  have hproduct := hfactor.mul hinside
  have hzero : Tendsto
      (fun x =>
        (1 - (2 : ℝ) ^ (-smoothRankinSigma (X x) (y x)))⁻¹ *
          ((smoothPrimeCountingConstant * smoothRankinRatio (X x) (y x) /
              Real.log (y x) +
            smoothPrimeCountingConstant * smoothRankinSigma (X x) (y x) *
              ((5 * smoothRankinRatio (X x) (y x) /
                Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
            Real.log (taoZ x)))
      atTop (𝓝 0) := by
    simpa using hproduct
  apply hzero.congr'
  filter_upwards with x
  simp only [smoothDyadicSaddleError]
  ring

/-- The complete optimized dyadic Rankin exponent has the source-normalized
limit `-1/α`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_dyadicSaddleExponent_div_log_taoZ
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun x =>
      (-smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) +
        smoothDyadicSaddleError (X x) (y x)) /
          Real.log (taoZ x)) atTop (𝓝 (-(1 / α))) := by
  have hsaving :=
    (hregime.tendsto_rankinRatio_mul_log_div_log_taoZ hα).neg
  have herror :=
    hregime.tendsto_smoothDyadicSaddleError_div_log_taoZ_zero hα
  have hsum := hsaving.add herror
  have hlimit : Tendsto (fun x =>
      -(smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) /
            Real.log (taoZ x)) +
        smoothDyadicSaddleError (X x) (y x) / Real.log (taoZ x))
      atTop (𝓝 (-(1 / α))) := by
    simpa using hsum
  apply hlimit.congr'
  filter_upwards with x
  ring

/-- Full scalar dyadic Rankin estimate in Tao's critical source regime, with
all elementary saddle-range and depth hypotheses discharged. -/
theorem IsTaoCriticalSmoothRegime.eventually_smoothExponentialHarmonicSum_dyadic_le
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop,
      smoothExponentialHarmonicSum (smoothDyadicSteps (y x))
          (1 - smoothRankinSigma (X x) (y x)) ≤
        5 * smoothRankinRatio (X x) (y x) /
          Real.log (smoothRankinRatio (X x) (y x)) := by
  exact eventually_smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    X y hregime.eventually_two_le_X (hregime.eventually_two_le_y hα)
      (hregime.eventually_one_lt_rankinRatio hα)
      (hregime.eventually_smoothRankinSigma_nonneg hα)
      (hregime.tendsto_rankinRatio_atTop hα)
      (hregime.eventually_logScale_le_rankinRatio_sq hα)

/-- The critical-regime scalar estimate inserted into the actual finite
smooth-number Rankin bound. -/
theorem IsTaoCriticalSmoothRegime.eventually_psiNat_cast_le_dyadicSaddleRankin
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ x in atTop,
      (psiNat (X x) (y x) : ℝ) ≤ (X x : ℝ) * Real.exp
        (-smoothRankinRatio (X x) (y x) *
            Real.log (smoothRankinRatio (X x) (y x)) +
          smoothDyadicSaddleError (X x) (y x)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_one_lt_rankinRatio hα,
    hregime.eventually_smoothRankinSigma_pos hα,
    hregime.eventually_smoothExponentialHarmonicSum_dyadic_le hα] with
      x hX hy huOne hsigma hscalar
  exact psiNat_cast_le_self_mul_exp_dyadicSaddleRankinExponent
    hX hy huOne hsigma hscalar

/-- Quantified upper half of Proposition 2.1(i): every fixed positive slack
gives the source exponent `z^(-1/α+ε)`. -/
theorem IsTaoCriticalSmoothRegime.eventually_psiNat_cast_le_self_mul_exp_neg_log_taoZ
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (psiNat (X x) (y x) : ℝ) ≤ (X x : ℝ) * Real.exp
        (-(1 / α - ε) * Real.log (taoZ x)) := by
  have hnormalized :=
    hregime.tendsto_dyadicSaddleExponent_div_log_taoZ hα
  have hthreshold : -(1 / α) < -(1 / α - ε) := by linarith
  have hexponent : ∀ᶠ x in atTop,
      (-smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) +
        smoothDyadicSaddleError (X x) (y x)) /
          Real.log (taoZ x) < -(1 / α - ε) :=
    hnormalized.eventually (Iio_mem_nhds hthreshold)
  filter_upwards [hregime.eventually_psiNat_cast_le_dyadicSaddleRankin hα,
    hexponent,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with
      x hpsi hexponent' hzOne
  have hexponentBound :
      -smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) +
        smoothDyadicSaddleError (X x) (y x) ≤
      -(1 / α - ε) * Real.log (taoZ x) := by
    exact ((div_lt_iff₀ (Real.log_pos hzOne)).mp hexponent').le
  exact hpsi.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexponentBound) (Nat.cast_nonneg _))

/-- Source-shaped `z`-power form of the critical smooth-number upper bound. -/
theorem IsTaoCriticalSmoothRegime.eventually_psiNat_cast_le_self_div_taoZ_rpow
    {X y : ℕ → ℕ} {α ε : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (psiNat (X x) (y x) : ℝ) ≤
        (X x : ℝ) / (taoZ x) ^ (1 / α - ε) := by
  filter_upwards [
    hregime.eventually_psiNat_cast_le_self_mul_exp_neg_log_taoZ hα hε] with
      x hx
  calc
    (psiNat (X x) (y x) : ℝ) ≤
        (X x : ℝ) * Real.exp (-(1 / α - ε) * Real.log (taoZ x)) := hx
    _ = (X x : ℝ) / (taoZ x) ^ (1 / α - ε) := by
      rw [Real.rpow_def_of_pos (taoZ_pos x)]
      change (X x : ℝ) * Real.exp (-(1 / α - ε) * Real.log (taoZ x)) =
        (X x : ℝ) * (Real.exp (Real.log (taoZ x) * (1 / α - ε)))⁻¹
      rw [← Real.exp_neg]
      congr 2
      ring

end

end Tao2026
