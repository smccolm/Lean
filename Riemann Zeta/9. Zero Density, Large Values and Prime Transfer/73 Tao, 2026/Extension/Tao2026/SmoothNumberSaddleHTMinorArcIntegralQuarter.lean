import Tao2026.SmoothNumberSaddleHTMinorArcIntegral
import Tao2026.SmoothNumberSaddleHTMinorArcQuarter

/-!
# Weighted integration through the quarter-epsilon HT ceiling

The reciprocal physical Perron kernel makes the cost of raising the
frequency ceiling logarithmic.  At `epsilon = 1/4` that logarithmic cost is
still only polynomial and is absorbed by the HT stretched exponential.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Interval

namespace Tao2026

noncomputable section

theorem smoothSaddleHTFrequencyCeiling_quarter (y : ℕ) :
    smoothSaddleHTFrequencyCeiling y (1 / 4) =
      Real.exp ((Real.log y) ^ (5 / 4 : ℝ)) := by
  unfold smoothSaddleHTFrequencyCeiling
  norm_num

/-- A fixed seventh power is absorbed by the HT scale
`exp (-a*u/(log u)^2)`. -/
theorem tendsto_pow_seven_mul_exp_neg_self_div_log_sq_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => u n ^ (7 : ℕ) *
      Real.exp (-a * (u n / Real.log (u n) ^ 2))) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (u n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hu
  have hupper : Tendsto (fun n =>
      (Real.sqrt (u n)) ^ (14 : ℝ) * Real.exp (-a * Real.sqrt (u n)))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 14 a ha).comp hsqrt
  have hlogSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 4)).def (by norm_num : (0 : ℝ) < 1)
  have hnonneg : ∀ᶠ n in atTop, 0 ≤ u n ^ (7 : ℕ) *
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
  have hpow : (Real.sqrt (u n)) ^ (14 : ℝ) = u n ^ (7 : ℕ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul huPos.le]
    norm_num [Real.rpow_natCast]
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hexp (pow_nonneg huPos.le _)

/-- The logarithmic envelope for weighted HT integration through
`exp ((log y)^(5/4))`. -/
noncomputable def smoothSaddleHTMinorArcPerronEnvelopeQuarter
    (X y : ℕ) : ℝ :=
  (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
    (2 * (Real.exp (-(smoothSaddleHTMinorArcCoefficient *
        smoothSaddleHildebrandTenenbaumLoss X y
          (1 / Real.log (y : ℝ)))) * smoothSaddlePoint X y) *
      Real.log (smoothSaddleHTFrequencyCeiling y (1 / 4) /
        (1 / Real.log (y : ℝ))))

/-- The weighted envelope remains vanishing after enlarging the HT ceiling
to the quarter-epsilon height. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTMinorArcPerronEnvelopeQuarter_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTMinorArcPerronEnvelopeQuarter (X n) (y n))
      atTop (𝓝 0) := by
  let c := smoothSaddleHTMinorArcCoefficient
  let a := c / 65
  let C := 4 * Real.sqrt 7 / Real.sqrt (2 * Real.pi)
  have hc : 0 < c := by
    dsimp [c]
    exact smoothSaddleHTMinorArcCoefficient_pos
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdecay := tendsto_pow_seven_mul_exp_neg_self_div_log_sq_zero
    (hregime.tendsto_rankinRatio_atTop hα) ha
  have hupper : Tendsto (fun n => C *
      (smoothRankinRatio (X n) (y n) ^ (7 : ℕ) *
        Real.exp (-a * (smoothRankinRatio (X n) (y n) /
          Real.log (smoothRankinRatio (X n) (y n)) ^ 2))))
      atTop (𝓝 0) := by
    simpa using hdecay.const_mul C
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hregime.eventually_two_le_X,
      hregime.eventually_two_le_y hα,
      (hregime.tendsto_log_y_atTop hα).eventually
        (eventually_ge_atTop (1 : ℝ))] with n hX hy hL
    have hlogPos : 0 < Real.log (y n : ℝ) := by linarith
    have hceil : 1 ≤ smoothSaddleHTFrequencyCeiling (y n) (1 / 4) := by
      rw [smoothSaddleHTFrequencyCeiling_quarter]
      exact Real.one_le_exp (Real.rpow_nonneg hlogPos.le _)
    have hratio : 1 ≤ smoothSaddleHTFrequencyCeiling (y n) (1 / 4) /
        (1 / Real.log (y n : ℝ)) := by
      rw [show smoothSaddleHTFrequencyCeiling (y n) (1 / 4) /
          (1 / Real.log (y n : ℝ)) =
        smoothSaddleHTFrequencyCeiling (y n) (1 / 4) *
          Real.log (y n : ℝ) by field_simp]
      nlinarith
    unfold smoothSaddleHTMinorArcPerronEnvelopeQuarter
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
    have hsigmaLe : sigma ≤ 1 := by dsimp [sigma]; exact hsigmaOne.le
    have hLle : L ≤ u ^ (2 : ℕ) := by
      have huSq : 0 < u ^ (2 : ℕ) := pow_pos hu _
      apply (div_lt_one huSq).mp at hLratio
      exact hLratio.le
    have hlogL : Real.log L ≤ L := by
      have := Real.log_le_sub_one_of_pos hL
      linarith
    have hLpow : L ^ (5 / 4 : ℝ) ≤ L ^ (2 : ℕ) := by
      calc
        L ^ (5 / 4 : ℝ) ≤ L ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
        _ = L ^ (2 : ℕ) := by norm_num [Real.rpow_natCast]
    have hheightLog : Real.log
        (smoothSaddleHTFrequencyCeiling (y n) (1 / 4) / (1 / L)) ≤
          2 * L ^ (2 : ℕ) := by
      rw [smoothSaddleHTFrequencyCeiling_quarter,
        show Real.exp (Real.log (y n : ℝ) ^ (5 / 4 : ℝ)) / (1 / L) =
          Real.exp (Real.log (y n : ℝ) ^ (5 / 4 : ℝ)) * L by
            field_simp,
        Real.log_mul (Real.exp_pos _).ne' hL.ne', Real.log_exp]
      change L ^ (5 / 4 : ℝ) + Real.log L ≤ 2 * L ^ (2 : ℕ)
      have hLsq : L ≤ L ^ (2 : ℕ) := by nlinarith
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
        (smoothSaddleHTFrequencyCeiling (y n) (1 / 4) / (1 / L)) := by
      apply Real.log_nonneg
      rw [show smoothSaddleHTFrequencyCeiling (y n) (1 / 4) / (1 / L) =
        smoothSaddleHTFrequencyCeiling (y n) (1 / 4) * L by field_simp]
      have hceil : 1 ≤ smoothSaddleHTFrequencyCeiling (y n) (1 / 4) := by
        rw [smoothSaddleHTFrequencyCeiling_quarter]
        exact Real.one_le_exp (Real.rpow_nonneg hL.le _)
      nlinarith
    unfold smoothSaddleHTMinorArcPerronEnvelopeQuarter
    change (smoothSaddleStandardDeviation (X n) (y n) /
        Real.sqrt (2 * Real.pi)) *
      (2 * (Real.exp (-(c * loss)) * sigma) *
        Real.log (smoothSaddleHTFrequencyCeiling (y n) (1 / 4) /
          (1 / L))) ≤
      C * (u ^ (7 : ℕ) * Real.exp (-a * (u / v ^ 2)))
    calc
      (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
        (2 * (Real.exp (-(c * loss)) * sigma) *
          Real.log (smoothSaddleHTFrequencyCeiling (y n) (1 / 4) /
            (1 / L))) ≤
        (L * Real.sqrt (7 * u) / Real.sqrt (2 * Real.pi)) *
          (2 * (Real.exp (-a * (u / v ^ 2)) * 1) *
            (2 * L ^ (2 : ℕ))) := by
        gcongr
      _ = C * (L ^ (3 : ℕ) * Real.sqrt u *
          Real.exp (-a * (u / v ^ 2))) := by
        rw [hsqrtMul]
        dsimp [C]
        ring
      _ ≤ C * (u ^ (7 : ℕ) * Real.exp (-a * (u / v ^ 2))) := by
        gcongr
        calc
          L ^ (3 : ℕ) * Real.sqrt u ≤
              (u ^ (2 : ℕ)) ^ (3 : ℕ) * Real.sqrt u := by
            gcongr
          _ ≤ u ^ (7 : ℕ) := by
            rw [show (u ^ (2 : ℕ)) ^ (3 : ℕ) = u ^ (6 : ℕ) by ring,
              show u ^ (7 : ℕ) = u ^ (6 : ℕ) * u by ring]
            exact mul_le_mul_of_nonneg_left hsqrtU (pow_nonneg hu.le _)

/-- The complete finite symmetric Perron contribution through the
quarter-epsilon HT ceiling. -/
noncomputable def smoothSaddleHTMinorArcPerronContributionQuarter
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (1 / Real.log (y : ℝ))
    (smoothSaddleHTFrequencyCeiling y (1 / 4))

/-- The enlarged unconditional HT minor arc has vanishing normalized
Perron mass in every Tao-critical smooth regime. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTMinorArcPerronContributionQuarter_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTMinorArcPerronContributionQuarter
      (X n) (y n)) atTop (𝓝 0) := by
  have henvelope :=
    hregime.tendsto_smoothSaddleHTMinorArcPerronEnvelopeQuarter_zero hα
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    henvelope
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    hregime.eventually_smoothSaddleHTMinorArcBoundAt_quarter hα] with
      n hX hy hlogY hminor
  have hlogPos : 0 < Real.log (y n : ℝ) := by linarith
  have hlower : 0 < 1 / Real.log (y n : ℝ) := one_div_pos.mpr hlogPos
  have hceil : 1 ≤ smoothSaddleHTFrequencyCeiling (y n) (1 / 4) := by
    rw [smoothSaddleHTFrequencyCeiling_quarter]
    exact Real.one_le_exp (Real.rpow_nonneg hlogPos.le _)
  have hlu : 1 / Real.log (y n : ℝ) ≤
      smoothSaddleHTFrequencyCeiling (y n) (1 / 4) := by
    have hone : 1 / Real.log (y n : ℝ) ≤ 1 :=
      (div_le_one hlogPos).2 hlogY
    exact hone.trans hceil
  unfold smoothSaddleHTMinorArcPerronContributionQuarter
  exact norm_smoothSaddleSymmetricPerronShellContribution_le_ht_log
    hX hy smoothSaddleHTMinorArcCoefficient_pos.le hlower hlu hminor

/-- The exact enlarged outer segment from the established wide Perron
height to the quarter-epsilon HT ceiling. -/
noncomputable def smoothSaddleHTOuterPerronContributionQuarter
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleWidePerronHeight X y)
    (smoothSaddleHTFrequencyCeiling y (1 / 4))

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTOuterPerronContributionQuarter_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHTOuterPerronContributionQuarter
      (X n) (y n)) atTop (𝓝 0) := by
  have hdiff :=
    (hregime.tendsto_smoothSaddleHTMinorArcPerronContributionQuarter_zero hα).sub
      (hregime.tendsto_smoothSaddleHTInitialOverlapPerronContribution_zero hα)
  have hdiff' : Tendsto (fun n =>
      smoothSaddleHTMinorArcPerronContributionQuarter (X n) (y n) -
        smoothSaddleHTInitialOverlapPerronContribution (X n) (y n))
      atTop (𝓝 0) := by simpa using hdiff
  apply hdiff'.congr'
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα] with n hX hy
  unfold smoothSaddleHTMinorArcPerronContributionQuarter
    smoothSaddleHTInitialOverlapPerronContribution
    smoothSaddleHTOuterPerronContributionQuarter
  have hadd := smoothSaddleSymmetricPerronShellContribution_add_adjacent
    hX hy (1 / Real.log (y n : ℝ))
      (smoothSaddleWidePerronHeight (X n) (y n))
      (smoothSaddleHTFrequencyCeiling (y n) (1 / 4))
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using hadd.symm

end

end Tao2026
