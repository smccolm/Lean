import Tao2026.SmoothNumberSourceRegimes

/-!
# Polylogarithmic source regimes for Tao's smooth-number estimate

This module encodes the second regime in Proposition 2.1,
`X = x^(1+o(1))` and `y = log(x)^(A+o(1))`, and connects it to the exact
Rankin saddle variables.
-/

open Filter Topology

namespace Tao2026

noncomputable section

/-- The natural Rankin ratio scale in the polylogarithmic regime.  Defining
it through `u₀` makes its divergence immediate; below it is identified with
`log x / log₂ x`. -/
def taoPolylogUZero (x : ℕ) : ℝ := taoUZero x ^ (2 : ℕ) / 2

theorem taoPolylogUZero_eq_log_div_iteratedLog
    {x : ℕ} (hlog : 0 < Real.log x) (hiter : 0 < iteratedLog x) :
    taoPolylogUZero x = Real.log x / iteratedLog x := by
  rw [taoPolylogUZero, taoUZero]
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt hlog.le, Real.sq_sqrt hiter.le]
  field_simp [hiter.ne']

theorem tendsto_taoPolylogUZero_atTop :
    Tendsto taoPolylogUZero atTop atTop := by
  have hsquare : Tendsto (fun x : ℕ => taoUZero x ^ (2 : ℕ)) atTop atTop := by
    simpa [pow_two] using
      tendsto_taoUZero_atTop.atTop_mul_atTop₀ tendsto_taoUZero_atTop
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have h := hsquare.const_mul_atTop hhalf
  apply h.congr'
  filter_upwards with x
  simp [taoPolylogUZero]
  ring

/-- Exact filter contract for `X=x^(1+o(1))` and
`y=log(x)^(A+o(1))`. -/
def IsTaoPolylogSmoothRegime
    (X y : ℕ → ℕ) (A : ℝ) : Prop :=
  Tendsto (fun x => Real.log (X x) / Real.log x) atTop (𝓝 1) ∧
    Tendsto (fun x => Real.log (y x) / iteratedLog x) atTop (𝓝 A)

/-- In the polylogarithmic regime, the Rankin ratio normalized by
`log x/log₂ x` tends to `1/A`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_rankinRatio_div_taoPolylogUZero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => smoothRankinRatio (X x) (y x) /
      taoPolylogUZero x) atTop (𝓝 (1 / A)) := by
  have hratio := hregime.1.div hregime.2 hA.ne'
  apply hratio.congr'
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyRatioPos : ∀ᶠ x in atTop,
      0 < Real.log (y x) / iteratedLog x :=
    hregime.2.eventually (Ioi_mem_nhds hA)
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    hyRatioPos] with x hlogPos hiterPos hyRatioPos'
  have hyLogNe : Real.log (y x) ≠ 0 := by
    intro hyZero
    rw [hyZero, zero_div] at hyRatioPos'
    linarith
  change
    (Real.log (X x) / Real.log x) /
        (Real.log (y x) / iteratedLog x) =
      smoothRankinRatio (X x) (y x) / taoPolylogUZero x
  rw [taoPolylogUZero_eq_log_div_iteratedLog hlogPos hiterPos]
  unfold smoothRankinRatio
  field_simp [hlogPos.ne', hiterPos.ne', hyLogNe]

theorem IsTaoPolylogSmoothRegime.tendsto_rankinRatio_atTop
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => smoothRankinRatio (X x) (y x)) atTop atTop := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoPolylogUZero hA
  have hproduct := hnormalized.pos_mul_atTop (one_div_pos.mpr hA)
    tendsto_taoPolylogUZero_atTop
  apply hproduct.congr'
  filter_upwards [tendsto_taoPolylogUZero_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x huPos
  field_simp [huPos.ne']

/-- The logarithm of the polylogarithmic Rankin scale is asymptotic to
`log₂ x`. -/
theorem tendsto_log_taoPolylogUZero_div_iteratedLog_one :
    Tendsto (fun x : ℕ =>
      Real.log (taoPolylogUZero x) / iteratedLog x) atTop (𝓝 1) := by
  have htwice :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul
      tendsto_log_taoUZero_div_iteratedLog
  have hlogTwo : Tendsto (fun x : ℕ =>
      Real.log 2 / iteratedLog x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_iteratedLog_atTop
  have hlimit := htwice.sub hlogTwo
  have hlimitOne : Tendsto (fun x : ℕ =>
      2 * (Real.log (taoUZero x) / iteratedLog x) -
        Real.log 2 / iteratedLog x) atTop (𝓝 1) := by
    simpa using hlimit
  apply hlimitOne.congr'
  filter_upwards [tendsto_taoUZero_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x huZeroPos hiterPos
  rw [taoPolylogUZero, Real.log_div
    (pow_ne_zero _ huZeroPos.ne') (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_pow]
  field_simp [hiterPos.ne']
  ring

/-- Consequently `log u/log₂ x → 1` for every fixed positive `A`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_log_rankinRatio_div_iteratedLog_one
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (smoothRankinRatio (X x) (y x)) /
      iteratedLog x) atTop (𝓝 1) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoPolylogUZero hA
  have hlogNormalized : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoPolylogUZero x))
      atTop (𝓝 (Real.log (1 / A))) :=
    (Real.continuousAt_log (one_div_ne_zero hA.ne')).tendsto.comp hnormalized
  have hcorrection := hlogNormalized.div_atTop tendsto_iteratedLog_atTop
  have hsum := hcorrection.add tendsto_log_taoPolylogUZero_div_iteratedLog_one
  have hsumOne : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x) / taoPolylogUZero x) /
          iteratedLog x +
        Real.log (taoPolylogUZero x) / iteratedLog x) atTop (𝓝 1) := by
    simpa using hsum
  apply hsumOne.congr'
  filter_upwards [hnormalized.eventually (Ioi_mem_nhds (one_div_pos.mpr hA)),
    tendsto_taoPolylogUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with x hnormPos huZeroPos
  have hproduct :
      (smoothRankinRatio (X x) (y x) / taoPolylogUZero x) *
          taoPolylogUZero x = smoothRankinRatio (X x) (y x) := by
    field_simp [huZeroPos.ne']
  have hlogProduct :
      Real.log (smoothRankinRatio (X x) (y x)) =
        Real.log (smoothRankinRatio (X x) (y x) / taoPolylogUZero x) +
          Real.log (taoPolylogUZero x) := by
    conv_lhs => rw [← hproduct]
    rw [Real.log_mul hnormPos.ne' huZeroPos.ne']
  rw [hlogProduct]
  ring

/-- The standard saddle converges to the positive constant `1-1/A`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_smoothRankinSigma
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => smoothRankinSigma (X x) (y x))
      atTop (𝓝 (1 - 1 / A)) := by
  have hquotient :=
    (hregime.tendsto_log_rankinRatio_div_iteratedLog_one hA).div
      hregime.2 hA.ne'
  have hratio : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x)) / Real.log (y x))
      atTop (𝓝 (1 / A)) := by
    apply hquotient.congr'
    filter_upwards [tendsto_iteratedLog_atTop.eventually
        (eventually_gt_atTop (0 : ℝ)),
      hregime.2.eventually (Ioi_mem_nhds hA)] with x hiterPos hyRatioPos
    have hyLogNe : Real.log (y x) ≠ 0 := by
      intro hyZero
      rw [hyZero, zero_div] at hyRatioPos
      linarith
    change
      (Real.log (smoothRankinRatio (X x) (y x)) / iteratedLog x) /
          (Real.log (y x) / iteratedLog x) =
        Real.log (smoothRankinRatio (X x) (y x)) / Real.log (y x)
    field_simp [hiterPos.ne', hyLogNe]
  have h :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      hratio
  simpa [smoothRankinSigma] using h

/-- When `A>1`, the polylogarithmic saddle is eventually strictly inside
the Rankin range. -/
theorem IsTaoPolylogSmoothRegime.eventually_smoothRankinSigma_pos
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    ∀ᶠ x in atTop, 0 < smoothRankinSigma (X x) (y x) := by
  have hlimitPos : 0 < 1 - 1 / A := by
    rw [sub_pos, div_lt_one (lt_trans zero_lt_one hA)]
    exact hA
  exact (hregime.tendsto_smoothRankinSigma (lt_trans zero_lt_one hA)).eventually
    (Ioi_mem_nhds hlimitPos)

/-- The logarithmic source scale is negligible compared with the square of
the natural polylogarithmic Rankin scale. -/
theorem tendsto_iteratedLog_div_taoPolylogUZero_sq_zero :
    Tendsto (fun x : ℕ => iteratedLog x / taoPolylogUZero x ^ (2 : ℕ))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun x : ℕ =>
      iteratedLog x ^ (3 : ℝ) / (Real.log x) ^ (2 : ℝ)) atTop (𝓝 0) := by
    simpa [iteratedLog] using
      ((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
        (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero.comp hlog)
  apply hbase.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  rw [taoPolylogUZero_eq_log_div_iteratedLog hlogPos hiterPos]
  field_simp [hlogPos.ne', hiterPos.ne']
  simpa [Real.rpow_natCast] using
    (mul_comm (iteratedLog x ^ (3 : ℝ)) (Real.log x ^ (2 : ℝ)))

theorem IsTaoPolylogSmoothRegime.tendsto_log_y_div_rankinRatio_sq_zero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (y x) /
      smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoPolylogUZero hA
  have hnormalizedSq := hnormalized.pow 2
  have hlimitNe : (1 / A) ^ (2 : ℕ) ≠ 0 :=
    pow_ne_zero _ (one_div_ne_zero hA.ne')
  have hboundedRatio := hregime.2.div hnormalizedSq hlimitNe
  have hproduct := hboundedRatio.mul
    tendsto_iteratedLog_div_taoPolylogUZero_sq_zero
  have hproductZero : Tendsto (fun x =>
      (Real.log (y x) / iteratedLog x /
          (smoothRankinRatio (X x) (y x) / taoPolylogUZero x) ^ (2 : ℕ)) *
        (iteratedLog x / taoPolylogUZero x ^ (2 : ℕ))) atTop (𝓝 0) := by
    simpa using hproduct
  apply hproductZero.congr'
  have huTop := hregime.tendsto_rankinRatio_atTop hA
  have hyRatioPos : ∀ᶠ x in atTop, 0 < Real.log (y x) / iteratedLog x :=
    hregime.2.eventually (Ioi_mem_nhds hA)
  filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoPolylogUZero_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    huTop.eventually (eventually_gt_atTop (0 : ℝ)), hyRatioPos] with
      x hiterPos huZeroPos huPos hyRatioPos'
  have hyLogNe : Real.log (y x) ≠ 0 := by
    intro hyZero
    rw [hyZero, zero_div] at hyRatioPos'
    linarith
  field_simp [hiterPos.ne', huZeroPos.ne', huPos.ne', hyLogNe]

theorem IsTaoPolylogSmoothRegime.tendsto_log_two_mul_y_div_rankinRatio_sq_zero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (2 * (y x : ℝ)) /
      smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) := by
  have huTop := hregime.tendsto_rankinRatio_atTop hA
  have huSqTop : Tendsto
      (fun x => smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop atTop := by
    simpa [pow_two] using huTop.atTop_mul_atTop₀ huTop
  have hconst : Tendsto (fun x => Real.log 2 /
      smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop huSqTop
  have hsum := hconst.add (hregime.tendsto_log_y_div_rankinRatio_sq_zero hA)
  have hsumZero : Tendsto (fun x =>
      Real.log 2 / smoothRankinRatio (X x) (y x) ^ (2 : ℕ) +
        Real.log (y x) / smoothRankinRatio (X x) (y x) ^ (2 : ℕ))
      atTop (𝓝 0) := by
    simpa using hsum
  apply hsumZero.congr'
  have hyTop : Tendsto (fun x => Real.log (y x)) atTop atTop := by
    have hproduct := hregime.2.pos_mul_atTop hA tendsto_iteratedLog_atTop
    apply hproduct.congr'
    filter_upwards [tendsto_iteratedLog_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with x hiterPos
    field_simp [hiterPos.ne']
  filter_upwards [hyTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hyLogPos
  have hyPos : (0 : ℝ) < y x := by
    have hyOne : (1 : ℝ) < y x :=
      (Real.log_pos_iff (Nat.cast_nonneg _)).mp hyLogPos
    linarith
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hyPos.ne']
  ring

theorem IsTaoPolylogSmoothRegime.eventually_logScale_le_rankinRatio_sq
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    ∀ᶠ x in atTop,
      Real.log (2 * (y x : ℝ)) / Real.log 2 ≤
        smoothRankinRatio (X x) (y x) ^ (2 : ℕ) := by
  have hdecay : Tendsto (fun x =>
      (Real.log (2 * (y x : ℝ)) / Real.log 2) /
        smoothRankinRatio (X x) (y x) ^ (2 : ℕ)) atTop (𝓝 0) := by
    have h := (hregime.tendsto_log_two_mul_y_div_rankinRatio_sq_zero hA).const_mul
      (1 / Real.log 2)
    have hzero : Tendsto (fun x =>
        1 / Real.log 2 *
          (Real.log (2 * (y x : ℝ)) /
            smoothRankinRatio (X x) (y x) ^ (2 : ℕ))) atTop (𝓝 0) := by
      simpa using h
    apply hzero.congr'
    filter_upwards with x
    ring
  have huTop := hregime.tendsto_rankinRatio_atTop hA
  filter_upwards [hdecay.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    huTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx huPos
  rw [div_lt_iff₀ (sq_pos_of_pos huPos)] at hx
  simpa only [one_mul] using hx.le

theorem IsTaoPolylogSmoothRegime.tendsto_log_X_atTop
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) :
    Tendsto (fun x => Real.log (X x)) atTop atTop := by
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hproduct := hregime.1.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hlog
  apply hproduct.congr'
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp [hx.ne']

theorem IsTaoPolylogSmoothRegime.tendsto_log_y_atTop
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => Real.log (y x)) atTop atTop := by
  have hproduct := hregime.2.pos_mul_atTop hA tendsto_iteratedLog_atTop
  apply hproduct.congr'
  filter_upwards [tendsto_iteratedLog_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hiterPos
  field_simp [hiterPos.ne']

theorem IsTaoPolylogSmoothRegime.eventually_two_le_X
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) :
    ∀ᶠ x in atTop, 2 ≤ X x := by
  filter_upwards [hregime.tendsto_log_X_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  have hone : (1 : ℝ) < X x :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hx
  exact_mod_cast hone

theorem IsTaoPolylogSmoothRegime.eventually_two_le_y
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    ∀ᶠ x in atTop, 2 ≤ y x := by
  filter_upwards [hregime.tendsto_log_y_atTop hA |>.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  have hone : (1 : ℝ) < y x :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hx
  exact_mod_cast hone

theorem IsTaoPolylogSmoothRegime.eventually_one_lt_rankinRatio
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    ∀ᶠ x in atTop, 1 < smoothRankinRatio (X x) (y x) :=
  (hregime.tendsto_rankinRatio_atTop hA).eventually (eventually_gt_atTop 1)

theorem IsTaoPolylogSmoothRegime.eventually_smoothRankinSigma_nonneg
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    ∀ᶠ x in atTop, 0 ≤ smoothRankinSigma (X x) (y x) :=
  (hregime.eventually_smoothRankinSigma_pos hA).mono fun _ hx => hx.le

/-- The leading Rankin saving is `(1/A) log x`. -/
theorem IsTaoPolylogSmoothRegime.tendsto_rankinRatio_mul_log_div_log
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x =>
      smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) / Real.log x)
      atTop (𝓝 (1 / A)) := by
  have hproduct :=
    (hregime.tendsto_rankinRatio_div_taoPolylogUZero hA).mul
      (hregime.tendsto_log_rankinRatio_div_iteratedLog_one hA)
  have hlimit : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) / taoPolylogUZero x) *
        (Real.log (smoothRankinRatio (X x) (y x)) / iteratedLog x))
      atTop (𝓝 (1 / A)) := by
    simpa using hproduct
  apply hlimit.congr'
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  rw [taoPolylogUZero_eq_log_div_iteratedLog hlogPos hiterPos]
  field_simp [hlogPos.ne', hiterPos.ne']

/-- The Rankin ratio is lower order than the ambient logarithmic scale. -/
theorem IsTaoPolylogSmoothRegime.tendsto_rankinRatio_div_log_zero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 0 < A) :
    Tendsto (fun x => smoothRankinRatio (X x) (y x) / Real.log x)
      atTop (𝓝 0) := by
  have hnormalized := hregime.tendsto_rankinRatio_div_taoPolylogUZero hA
  have hinv : Tendsto (fun x : ℕ => (iteratedLog x)⁻¹) atTop (𝓝 0) :=
    tendsto_iteratedLog_atTop.inv_tendsto_atTop
  have hproduct := hnormalized.mul hinv
  have hzero : Tendsto (fun x =>
      (smoothRankinRatio (X x) (y x) / taoPolylogUZero x) *
        (iteratedLog x)⁻¹) atTop (𝓝 0) := by
    simpa using hproduct
  apply hzero.congr'
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hlogPos hiterPos
  rw [taoPolylogUZero_eq_log_div_iteratedLog hlogPos hiterPos]
  field_simp [hlogPos.ne', hiterPos.ne']

/-- The complete positive error in the compressed dyadic Rankin estimate is
`o(log x)` in the polylogarithmic regime. -/
theorem IsTaoPolylogSmoothRegime.tendsto_smoothDyadicSaddleError_div_log_zero
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    Tendsto (fun x => smoothDyadicSaddleError (X x) (y x) / Real.log x)
      atTop (𝓝 0) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  have hsigma := hregime.tendsto_smoothRankinSigma hAPos
  have hlimitPos : 0 < 1 - 1 / A := by
    rw [sub_pos, div_lt_one hAPos]
    exact hA
  have hrpow : Tendsto (fun x =>
      (2 : ℝ) ^ (-smoothRankinSigma (X x) (y x)))
      atTop (𝓝 ((2 : ℝ) ^ (-(1 - 1 / A)))) :=
    (Real.continuousAt_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp
      hsigma.neg
  have hdenominator :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hrpow
  have hrpowLt : (2 : ℝ) ^ (-(1 - 1 / A)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hlimitPos)
  have hdenominatorNe : 1 - (2 : ℝ) ^ (-(1 - 1 / A)) ≠ 0 :=
    (sub_pos.mpr hrpowLt).ne'
  have hfactor := hdenominator.inv₀ hdenominatorNe
  have huLog := hregime.tendsto_rankinRatio_div_log_zero hAPos
  have hyLogTop := hregime.tendsto_log_y_atTop hAPos
  have huLogTop : Tendsto (fun x =>
      Real.log (smoothRankinRatio (X x) (y x))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hAPos)
  have hyInv := hyLogTop.inv_tendsto_atTop
  have huInv := huLogTop.inv_tendsto_atTop
  have hAraw :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => smoothPrimeCountingConstant)
      atTop (𝓝 smoothPrimeCountingConstant)).mul huLog |>.mul hyInv
  have hArawZero : Tendsto
      (fun x => smoothPrimeCountingConstant *
        (smoothRankinRatio (X x) (y x) / Real.log x) *
          (Real.log (y x))⁻¹) atTop (𝓝 0) := by
    simpa using hAraw
  have hAterm : Tendsto
      (fun x => (smoothPrimeCountingConstant *
        smoothRankinRatio (X x) (y x) / Real.log (y x)) / Real.log x)
      atTop (𝓝 0) := by
    apply hArawZero.congr'
    filter_upwards [hyLogTop.eventually (eventually_gt_atTop (0 : ℝ))] with
        x hyLogPos
    field_simp [hyLogPos.ne']
  let D : ℝ := 5 * smoothPrimeCountingConstant / Real.log 2
  have hDraw : Tendsto (fun _ : ℕ => D) atTop (𝓝 D) := tendsto_const_nhds
  have hBraw := ((hDraw.mul hsigma).mul huLog).mul huInv
  have hBrawZero : Tendsto
      (fun x => D * smoothRankinSigma (X x) (y x) *
        (smoothRankinRatio (X x) (y x) / Real.log x) *
          (Real.log (smoothRankinRatio (X x) (y x)))⁻¹)
      atTop (𝓝 0) := by
    simpa using hBraw
  have hBterm : Tendsto
      (fun x => (smoothPrimeCountingConstant *
        smoothRankinSigma (X x) (y x) *
          ((5 * smoothRankinRatio (X x) (y x) /
            Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
          Real.log x) atTop (𝓝 0) := by
    apply hBrawZero.congr'
    filter_upwards [huLogTop.eventually (eventually_gt_atTop (0 : ℝ))] with
        x huLogPos
    dsimp only [D]
    field_simp [huLogPos.ne', (Real.log_pos one_lt_two).ne']
  have hinsideSum : Tendsto
      (fun x =>
        (smoothPrimeCountingConstant * smoothRankinRatio (X x) (y x) /
          Real.log (y x)) / Real.log x +
        (smoothPrimeCountingConstant * smoothRankinSigma (X x) (y x) *
          ((5 * smoothRankinRatio (X x) (y x) /
            Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
          Real.log x) atTop (𝓝 0) := by
    simpa using hAterm.add hBterm
  have hinside : Tendsto
      (fun x =>
        (smoothPrimeCountingConstant * smoothRankinRatio (X x) (y x) /
            Real.log (y x) +
          smoothPrimeCountingConstant * smoothRankinSigma (X x) (y x) *
            ((5 * smoothRankinRatio (X x) (y x) /
              Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
          Real.log x) atTop (𝓝 0) := by
    apply hinsideSum.congr'
    filter_upwards with x
    ring
  have hzero : Tendsto
      (fun x =>
        (1 - (2 : ℝ) ^ (-smoothRankinSigma (X x) (y x)))⁻¹ *
          ((smoothPrimeCountingConstant * smoothRankinRatio (X x) (y x) /
              Real.log (y x) +
            smoothPrimeCountingConstant * smoothRankinSigma (X x) (y x) *
              ((5 * smoothRankinRatio (X x) (y x) /
                Real.log (smoothRankinRatio (X x) (y x))) / Real.log 2)) /
            Real.log x)) atTop (𝓝 0) := by
    simpa using hfactor.mul hinside
  apply hzero.congr'
  filter_upwards with x
  simp only [smoothDyadicSaddleError]
  ring

theorem IsTaoPolylogSmoothRegime.tendsto_dyadicSaddleExponent_div_log
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    Tendsto (fun x =>
      (-smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) +
        smoothDyadicSaddleError (X x) (y x)) / Real.log x)
      atTop (𝓝 (-(1 / A))) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  have hsaving := (hregime.tendsto_rankinRatio_mul_log_div_log hAPos).neg
  have herror := hregime.tendsto_smoothDyadicSaddleError_div_log_zero hA
  have hsum := hsaving.add herror
  have hlimit : Tendsto (fun x =>
      -(smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) / Real.log x) +
        smoothDyadicSaddleError (X x) (y x) / Real.log x)
      atTop (𝓝 (-(1 / A))) := by
    simpa using hsum
  apply hlimit.congr'
  filter_upwards with x
  ring

theorem IsTaoPolylogSmoothRegime.eventually_smoothExponentialHarmonicSum_dyadic_le
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    ∀ᶠ x in atTop,
      smoothExponentialHarmonicSum (smoothDyadicSteps (y x))
          (1 - smoothRankinSigma (X x) (y x)) ≤
        5 * smoothRankinRatio (X x) (y x) /
          Real.log (smoothRankinRatio (X x) (y x)) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  exact eventually_smoothExponentialHarmonicSum_dyadic_le_five_mul_ratio_div_log
    X y hregime.eventually_two_le_X (hregime.eventually_two_le_y hAPos)
      (hregime.eventually_one_lt_rankinRatio hAPos)
      (hregime.eventually_smoothRankinSigma_nonneg hA)
      (hregime.tendsto_rankinRatio_atTop hAPos)
      (hregime.eventually_logScale_le_rankinRatio_sq hAPos)

theorem IsTaoPolylogSmoothRegime.eventually_psiNat_cast_le_dyadicSaddleRankin
    {X y : ℕ → ℕ} {A : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) :
    ∀ᶠ x in atTop,
      (psiNat (X x) (y x) : ℝ) ≤ (X x : ℝ) * Real.exp
        (-smoothRankinRatio (X x) (y x) *
            Real.log (smoothRankinRatio (X x) (y x)) +
          smoothDyadicSaddleError (X x) (y x)) := by
  have hAPos : 0 < A := lt_trans zero_lt_one hA
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hAPos,
    hregime.eventually_one_lt_rankinRatio hAPos,
    hregime.eventually_smoothRankinSigma_pos hA,
    hregime.eventually_smoothExponentialHarmonicSum_dyadic_le hA] with
      x hX hy huOne hsigma hscalar
  exact psiNat_cast_le_self_mul_exp_dyadicSaddleRankinExponent
    hX hy huOne hsigma hscalar

/-- Quantified upper half of Proposition 2.1(ii). -/
theorem IsTaoPolylogSmoothRegime.eventually_psiNat_cast_le_self_mul_exp_neg_log
    {X y : ℕ → ℕ} {A ε : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (psiNat (X x) (y x) : ℝ) ≤ (X x : ℝ) * Real.exp
        (-(1 / A - ε) * Real.log x) := by
  have hnormalized := hregime.tendsto_dyadicSaddleExponent_div_log hA
  have hthreshold : -(1 / A) < -(1 / A - ε) := by linarith
  have hexponent : ∀ᶠ x in atTop,
      (-smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) +
        smoothDyadicSaddleError (X x) (y x)) / Real.log x <
          -(1 / A - ε) :=
    hnormalized.eventually (Iio_mem_nhds hthreshold)
  have hlog : Tendsto (fun x : ℕ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hregime.eventually_psiNat_cast_le_dyadicSaddleRankin hA,
    hexponent, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hpsi hexponent' hlogPos
  have hexponentBound :
      -smoothRankinRatio (X x) (y x) *
          Real.log (smoothRankinRatio (X x) (y x)) +
        smoothDyadicSaddleError (X x) (y x) ≤
      -(1 / A - ε) * Real.log x :=
    ((div_lt_iff₀ hlogPos).mp hexponent').le
  exact hpsi.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hexponentBound) (Nat.cast_nonneg _))

theorem IsTaoPolylogSmoothRegime.eventually_psiNat_cast_le_self_div_rpow
    {X y : ℕ → ℕ} {A ε : ℝ}
    (hregime : IsTaoPolylogSmoothRegime X y A) (hA : 1 < A) (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      (psiNat (X x) (y x) : ℝ) ≤ (X x : ℝ) / (x : ℝ) ^ (1 / A - ε) := by
  have hxTop : Tendsto (fun x : ℕ => (x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hregime.eventually_psiNat_cast_le_self_mul_exp_neg_log hA hε,
    hxTop.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hxPos
  calc
    (psiNat (X x) (y x) : ℝ) ≤
        (X x : ℝ) * Real.exp (-(1 / A - ε) * Real.log x) := hx
    _ = (X x : ℝ) / (x : ℝ) ^ (1 / A - ε) := by
      rw [Real.rpow_def_of_pos hxPos]
      change (X x : ℝ) * Real.exp (-(1 / A - ε) * Real.log x) =
        (X x : ℝ) * (Real.exp (Real.log x * (1 / A - ε)))⁻¹
      rw [← Real.exp_neg]
      congr 2
      ring

end

end Tao2026
