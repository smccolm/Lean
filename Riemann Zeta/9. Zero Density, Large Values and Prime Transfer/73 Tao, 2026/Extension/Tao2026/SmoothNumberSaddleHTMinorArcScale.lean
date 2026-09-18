import Tao2026.SmoothNumberSaddleHTMinorArc
import Tao2026.SmoothNumberSaddleCurvatureLower
import Tao2026.SmoothNumberSaddleIndexedLossScale

/-!
# Critical scale for the HT minor arc

At the first physical outer frequency `1 / log y`, the rational HT loss is
already at least a constant multiple of `u / (log u)^2`.  This scale tends to
infinity in every Tao-critical smooth regime.  Radial monotonicity will then
make the same lower bound available throughout the HT frequency range.
-/

open Filter Topology Set

namespace Tao2026

noncomputable section

/-- The critical Rankin ratio is negligible compared with `log y`. -/
theorem IsTaoCriticalSmoothRegime.tendsto_rankinRatio_div_log_y_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothRankinRatio (X n) (y n) / Real.log (y n))
      atTop (𝓝 0) := by
  have hquot := (hregime.tendsto_rankinRatio_div_log_taoZ_zero hα).div
    hregime.2 hα.ne'
  have hquot' : Tendsto (fun n =>
      (smoothRankinRatio (X n) (y n) / Real.log (taoZ n)) /
        (Real.log (y n) / Real.log (taoZ n))) atTop (𝓝 0) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [tendsto_taoZ_atTop.eventually
      (eventually_gt_atTop (1 : ℝ)),
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_gt_atTop (0 : ℝ))] with n hzOne hyLog
  field_simp [(Real.log_pos hzOne).ne', hyLog.ne']

theorem IsTaoCriticalSmoothRegime.eventually_rankinRatio_le_log_y
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothRankinRatio (X n) (y n) ≤ Real.log (y n) := by
  have hratio := (hregime.tendsto_rankinRatio_div_log_y_zero hα).eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hratio,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_gt_atTop (0 : ℝ))] with n hn hlog
  exact (div_lt_one hlog).mp hn |>.le

/-- The first outer physical frequency sees the scale
`u / (65 * (log u)^2)`. -/
theorem smoothRankinRatio_div_log_sq_le_smoothSaddleHTLoss_firstOuter
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hlogY : 0 < Real.log (y : ℝ))
    (hlogU : 1 ≤ Real.log (smoothRankinRatio X y))
    (hsigmaOne : smoothSaddlePoint X y ≤ 1)
    (hdisplacement : 1 - smoothSaddlePoint X y ≤
      8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ)) :
    smoothRankinRatio X y /
        (65 * Real.log (smoothRankinRatio X y) ^ 2) ≤
      smoothSaddleHildebrandTenenbaumLoss X y
        (1 / Real.log (y : ℝ)) := by
  let u := smoothRankinRatio X y
  let L := Real.log (y : ℝ)
  let v := Real.log u
  let beta := 1 - smoothSaddlePoint X y
  have hu : 0 < u := by dsimp [u]; exact smoothRankinRatio_pos hX hy
  have hv : 0 < v := by dsimp [v]; linarith
  have hbeta : 0 ≤ beta := by dsimp [beta]; linarith
  have hupper : 0 ≤ 8 * v / L := by positivity
  have hbetaSq : beta ^ 2 ≤ (8 * v / L) ^ 2 := by
    exact (sq_le_sq₀ hbeta hupper).2
      (by simpa only [beta, v, L] using hdisplacement)
  have hden : 0 < beta ^ 2 + (1 / L) ^ 2 := by positivity
  have hQ : 0 < 65 * v ^ 2 := by positivity
  have hdenLe : beta ^ 2 + (1 / L) ^ 2 ≤
      (65 * v ^ 2) * (1 / L) ^ 2 := by
    have hvSq : 1 ≤ v ^ 2 := by nlinarith
    calc
      beta ^ 2 + (1 / L) ^ 2 ≤
          (8 * v / L) ^ 2 + (1 / L) ^ 2 := add_le_add hbetaSq le_rfl
      _ = (64 * v ^ 2 + 1) * (1 / L) ^ 2 := by ring
      _ ≤ (65 * v ^ 2) * (1 / L) ^ 2 := by
        gcongr
        nlinarith
  unfold smoothSaddleHildebrandTenenbaumLoss
  change u / (65 * v ^ 2) ≤
    u * (1 / L) ^ 2 / (beta ^ 2 + (1 / L) ^ 2)
  rw [div_le_div_iff₀ hQ hden]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (mul_le_mul_of_nonneg_left hdenLe hu.le)

/-- The explicit first-frequency lower scale diverges. -/
theorem tendsto_rankinRatio_div_sixtyFive_log_sq_atTop
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => u n / (65 * Real.log (u n) ^ 2)) atTop atTop := by
  have hbase := tendsto_rpow_div_log_atTop hu
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hsq := hbase.atTop_mul_atTop₀ hbase
  have hscaled := hsq.const_mul_atTop (show (0 : ℝ) < 1 / 65 by norm_num)
  apply hscaled.congr'
  filter_upwards [hu.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  have hpow : (u n) ^ (1 / 2 : ℝ) * (u n) ^ (1 / 2 : ℝ) = u n := by
    calc
      (u n) ^ (1 / 2 : ℝ) * (u n) ^ (1 / 2 : ℝ) =
          (u n) ^ ((1 / 2 : ℝ) + 1 / 2) := (Real.rpow_add hn _ _).symm
      _ = u n := by norm_num
  change (1 / 65 : ℝ) *
      ((u n) ^ (1 / 2 : ℝ) / Real.log (u n) *
        ((u n) ^ (1 / 2 : ℝ) / Real.log (u n))) =
    u n / (65 * Real.log (u n) ^ 2)
  calc
    (1 / 65 : ℝ) *
        ((u n) ^ (1 / 2 : ℝ) / Real.log (u n) *
          ((u n) ^ (1 / 2 : ℝ) / Real.log (u n))) =
      (1 / 65 : ℝ) *
        (((u n) ^ (1 / 2 : ℝ) * (u n) ^ (1 / 2 : ℝ)) /
          Real.log (u n) ^ 2) := by ring
    _ = u n / (65 * Real.log (u n) ^ 2) := by rw [hpow]; ring

/-- In every critical regime, the HT loss at `1/log y` tends to infinity. -/
theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleHTLoss_firstOuter_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleHildebrandTenenbaumLoss (X n) (y n)
      (1 / Real.log (y n : ℝ))) atTop atTop := by
  have hlower := tendsto_rankinRatio_div_sixtyFive_log_sq_atTop
    (hregime.tendsto_rankinRatio_atTop hα)
  refine tendsto_atTop_mono' atTop ?_ hlower
  have hsaddleHalf := (hregime.tendsto_smoothSaddlePoint_one hα).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hlogU := (Real.tendsto_log_atTop.comp
    (hregime.tendsto_rankinRatio_atTop hα)).eventually
      (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_gt_atTop (0 : ℝ)),
    hlogU, hsaddleHalf,
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα] with
      n hX hy hlogY hlogU hsigmaHalf hsigmaOne hdisp
  exact smoothRankinRatio_div_log_sq_le_smoothSaddleHTLoss_firstOuter
    hX hy hlogY hlogU hsigmaOne.le hdisp.le

/-- The possible factor `y^(1-sigma)` in the HT error is killed by the
stretched-exponential saving when the critical Rankin ratio is at most
`log y`. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankin_pow_eight_mul_ht_decay_le_one
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothRankinRatio (X n) (y n) ^ (8 : ℕ) *
          Real.exp (-(Real.log (y n : ℝ)) ^ (1 / 4 : ℝ)) ≤ 1 := by
  have hpoly0 :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := Real.exp (-1)) (α := 0) (β := (1 / 4 : ℝ))
      (by norm_num) (by norm_num) 8
  have hpoly := (hregime.tendsto_y_atTop hα).eventually hpoly0
  filter_upwards [hregime.eventually_rankinRatio_le_log_y hα, hpoly,
    hregime.eventually_two_le_X, hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ))] with n huL hpoly hX hy hL
  let u := smoothRankinRatio (X n) (y n)
  let L := Real.log (y n : ℝ)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have huNonneg : 0 ≤ u := by
    dsimp [u]
    exact (smoothRankinRatio_pos hX hy).le
  rw [Real.rpow_natCast] at hpoly
  have hclean : L ^ (8 : ℕ) ≤ Real.exp (L ^ (1 / 4 : ℝ)) := by
    calc
      L ^ (8 : ℕ) = Real.exp (-1) * L ^ (8 : ℕ) * Real.exp 1 := by
        rw [show Real.exp (-1) * L ^ (8 : ℕ) * Real.exp 1 =
          L ^ (8 : ℕ) * (Real.exp (-1) * Real.exp 1) by ring,
          ← Real.exp_add]
        norm_num
      _ ≤ Real.exp (L ^ (1 / 4 : ℝ)) := by
        simpa only [L, Real.rpow_zero] using hpoly
  have hupow : u ^ (8 : ℕ) ≤ L ^ (8 : ℕ) := by
    exact pow_le_pow_left₀ huNonneg (by simpa only [u, L] using huL) 8
  calc
    u ^ (8 : ℕ) * Real.exp (-L ^ (1 / 4 : ℝ)) ≤
        Real.exp (L ^ (1 / 4 : ℝ)) *
          Real.exp (-L ^ (1 / 4 : ℝ)) := by
      gcongr
      exact hupow.trans hclean
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The standard critical saddle displacement bounds the Rankin factor in
the HT error by the eighth power of the Rankin ratio. -/
theorem smoothSaddle_rpow_le_rankinRatio_pow_eight
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hdisplacement : 1 - smoothSaddlePoint X y ≤
      8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ)) :
    (y : ℝ) ^ (1 - smoothSaddlePoint X y) ≤
      smoothRankinRatio X y ^ (8 : ℕ) := by
  let u := smoothRankinRatio X y
  let L := Real.log (y : ℝ)
  let beta := 1 - smoothSaddlePoint X y
  have hu : 0 < u := by dsimp [u]; exact smoothRankinRatio_pos hX hy
  have hyPos : 0 < (y : ℝ) := by positivity
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hbetaL : beta * L ≤ 8 * Real.log u := by
    apply (le_div_iff₀ hL).mp
    simpa only [beta, L, u] using hdisplacement
  rw [Real.rpow_def_of_pos hyPos]
  have hexp : Real.exp (Real.log (y : ℝ) * beta) ≤
      Real.exp (8 * Real.log u) := by
    apply Real.exp_le_exp.mpr
    simpa only [L, mul_comm] using hbetaL
  calc
    Real.exp (Real.log (y : ℝ) * beta) ≤
        Real.exp (8 * Real.log u) := hexp
    _ = u ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hu]
      norm_num
      ring_nf

/-- The saddle equation supplies the complementary lower bound for
`(1-sigma) log y`; the fixed source constant is harmless once `u` grows. -/
theorem IsTaoCriticalSmoothRegime.eventually_half_log_rankin_le_displacement_mul_log
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      (1 / 2 : ℝ) * Real.log (smoothRankinRatio (X n) (y n)) ≤
        (1 - smoothSaddlePoint (X n) (y n)) * Real.log (y n : ℝ) := by
  have hlogU : Tendsto
      (fun n => Real.log (smoothRankinRatio (X n) (y n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hlogU.eventually (eventually_ge_atTop
      (2 * Real.log (15 * Real.log 4)))] with
      n hX hy hlogY hsigmaHalf hsigmaOne hlogLarge
  let u := smoothRankinRatio (X n) (y n)
  let beta := 1 - smoothSaddlePoint (X n) (y n)
  have hu : 0 < u := by dsimp [u]; exact smoothRankinRatio_pos hX hy
  have hK : 0 < (15 * Real.log 4 : ℝ) := by positivity
  have hyPos : 0 < (y n : ℝ) := by positivity
  have hrpow := rankinRatio_div_fifteen_log_four_le_saddle_rpow
    hX hy hlogY hsigmaHalf.le hsigmaOne.le
  have hleftPos : 0 < u / (15 * Real.log 4) := div_pos hu hK
  have hrightPos : 0 < (y n : ℝ) ^ beta :=
    Real.rpow_pos_of_pos hyPos _
  have hlog := Real.strictMonoOn_log.monotoneOn
    hleftPos hrightPos (by simpa only [u, beta] using hrpow)
  rw [Real.log_div hu.ne' hK.ne', Real.log_rpow hyPos] at hlog
  dsimp [u, beta] at hlog ⊢
  linarith

/-- Once the Rankin factor is absorbed and the saddle displacement has its
natural lower scale, the normalized HT error is at most `4 / log u`. -/
theorem smoothSaddleHTMangoldtError_half_div_log_le_four_div_log_rankin
    {X y : ℕ} (hy : 2 ≤ y)
    (hlogU : 0 < Real.log (smoothRankinRatio X y))
    (hsigmaOne : smoothSaddlePoint X y < 1)
    (hdecay : (y : ℝ) ^ (1 - smoothSaddlePoint X y) *
      Real.exp (-(Real.log (y : ℝ)) ^ (1 / 4 : ℝ)) ≤ 1)
    (hbetaLog : (1 / 2 : ℝ) * Real.log (smoothRankinRatio X y) ≤
      (1 - smoothSaddlePoint X y) * Real.log (y : ℝ)) :
    smoothSaddleHTMangoldtError y (1 - smoothSaddlePoint X y) (1 / 2) /
        Real.log (y : ℝ) ≤
      4 / Real.log (smoothRankinRatio X y) := by
  let u := smoothRankinRatio X y
  let beta := 1 - smoothSaddlePoint X y
  let L := Real.log (y : ℝ)
  have hbeta : 0 < beta := by dsimp [beta]; linarith
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hv : 0 < Real.log u := by simpa only [u] using hlogU
  have hnumNonneg : 0 ≤
      1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 4 : ℝ)) := by
    positivity
  have hnumLe :
      1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 4 : ℝ)) ≤ 2 := by
    dsimp [beta, L] at hdecay ⊢
    linarith
  unfold smoothSaddleHTMangoldtError
  norm_num
  change (beta⁻¹ *
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 4 : ℝ)))) / L ≤
    4 / Real.log u
  rw [show (beta⁻¹ *
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 4 : ℝ)))) / L =
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 4 : ℝ))) /
        (beta * L) by field_simp]
  rw [div_le_div_iff₀ (mul_pos hbeta hL) hv]
  have hleft :
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 4 : ℝ))) *
          Real.log u ≤ 2 * Real.log u :=
    mul_le_mul_of_nonneg_right hnumLe hv.le
  have hbetaLog' : (1 / 2 : ℝ) * Real.log u ≤ beta * L := by
    simpa only [u, beta, L] using hbetaLog
  nlinarith

/-- Along a Tao-critical regime the Lemma-6 error, normalized by `log y`,
has the explicit vanishing upper bound `4 / log u`. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMangoldtError_half_div_log_le
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 2) /
            Real.log (y n : ℝ) ≤
        4 / Real.log (smoothRankinRatio (X n) (y n)) := by
  have hlogU : Tendsto
      (fun n => Real.log (smoothRankinRatio (X n) (y n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα,
    hregime.eventually_rankin_pow_eight_mul_ht_decay_le_one hα,
    hregime.eventually_half_log_rankin_le_displacement_mul_log hα,
    hlogU.eventually (eventually_gt_atTop (0 : ℝ))] with
      n hX hy hsigmaOne hdisp hpowDecay hbetaLog hlogU
  have hrpow := smoothSaddle_rpow_le_rankinRatio_pow_eight hX hy hdisp.le
  have hdecay : (y n : ℝ) ^
        (1 - smoothSaddlePoint (X n) (y n)) *
      Real.exp (-(Real.log (y n : ℝ)) ^ (1 / 4 : ℝ)) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le).trans hpowDecay
  exact smoothSaddleHTMangoldtError_half_div_log_le_four_div_log_rankin
    hy hlogU hsigmaOne hdecay hbetaLog

/-- A fixed normalized upper bound for the higher-prime-power contribution. -/
noncomputable def smoothSaddleHTPrimePowerNormalizedBound : ℝ :=
  12 * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ * Real.log 4

theorem smoothSaddleHTPrimePowerNormalizedBound_pos :
    0 < smoothSaddleHTPrimePowerNormalizedBound := by
  unfold smoothSaddleHTPrimePowerNormalizedBound
  have hq : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  positivity

/-- After division by `log y`, the prime-power remainder is uniformly
bounded throughout the saddle range `sigma >= 1/2`. -/
theorem two_mul_smoothSaddleHTPrimePowerRemainder_div_log_le
    {y : ℕ} {sigma : ℝ} (hy : 2 ≤ y)
    (hlog : 1 ≤ Real.log (y : ℝ))
    (hsigma : (1 / 2 : ℝ) ≤ sigma) :
    2 * smoothSaddleHTPrimePowerRemainder y sigma / Real.log (y : ℝ) ≤
      smoothSaddleHTPrimePowerNormalizedBound := by
  let q : ℝ := (2 : ℝ) ^ (-(1 / 2 : ℝ))
  let L := Real.log (y : ℝ)
  let K := Real.log 4
  have hL : 0 < L := by dsimp [L]; linarith
  have hq : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by norm_num)
  have hA : 0 ≤ 2 * (1 - q)⁻¹ := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfactor : 2 + L ≤ 3 * L := by dsimp [L] at hlog ⊢; linarith
  have hrem := smoothSaddleHTPrimePowerRemainder_le_log hy hsigma
  rw [div_le_iff₀ hL]
  calc
    2 * smoothSaddleHTPrimePowerRemainder y sigma ≤
        2 * ((2 * (1 - q)⁻¹) * (K * (2 + L))) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [q, K, L] using hrem) (by norm_num)
    _ ≤ 2 * ((2 * (1 - q)⁻¹) * (K * (3 * L))) := by
      gcongr
    _ = smoothSaddleHTPrimePowerNormalizedBound * L := by
      unfold smoothSaddleHTPrimePowerNormalizedBound
      dsimp [q, K]
      ring

/-- For every fixed positive Lemma-6 coefficient, the complete normalized
scalar error is eventually bounded by one fixed absolute quantity. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMinorArcScalarError_le_fixed
    {X y : ℕ → ℕ} {α C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hC : 0 ≤ C) :
    ∀ᶠ n in atTop,
      (2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 2) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ) ≤
      1 + smoothSaddleHTPrimePowerNormalizedBound := by
  have hlogU : Tendsto
      (fun n => Real.log (smoothRankinRatio (X n) (y n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
  filter_upwards [hregime.eventually_htMangoldtError_half_div_log_le hα,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hlogU.eventually (eventually_gt_atTop (0 : ℝ)),
    hlogU.eventually (eventually_ge_atTop (8 * C))] with
      n herror hy hlogY hsigmaHalf hlogU hlogLarge
  let E := smoothSaddleHTMangoldtError (y n)
    (1 - smoothSaddlePoint (X n) (y n)) (1 / 2)
  let R := smoothSaddleHTPrimePowerRemainder (y n)
    (smoothSaddlePoint (X n) (y n))
  let L := Real.log (y n : ℝ)
  let v := Real.log (smoothRankinRatio (X n) (y n))
  have hL : 0 < L := by dsimp [L]; linarith
  have hv : 0 < v := by simpa only [v] using hlogU
  have herror' : E / L ≤ 4 / v := by
    simpa only [E, L, v] using herror
  have hprime : 2 * R / L ≤ smoothSaddleHTPrimePowerNormalizedBound := by
    exact two_mul_smoothSaddleHTPrimePowerRemainder_div_log_le
      hy hlogY hsigmaHalf
  have hscaled : 2 * C * (E / L) ≤ 8 * C / v := by
    calc
      2 * C * (E / L) ≤ 2 * C * (4 / v) := by gcongr
      _ = 8 * C / v := by ring
  have hsmall : 8 * C / v ≤ 1 := by
    exact (div_le_one hv).2 (by simpa only [v] using hlogLarge)
  change (2 * C * E + 2 * R) / L ≤
    1 + smoothSaddleHTPrimePowerNormalizedBound
  calc
    (2 * C * E + 2 * R) / L =
        2 * C * (E / L) + 2 * R / L := by ring
    _ ≤ 8 * C / v + smoothSaddleHTPrimePowerNormalizedBound :=
      add_le_add hscaled hprime
    _ ≤ 1 + smoothSaddleHTPrimePowerNormalizedBound :=
      add_le_add hsmall le_rfl

/-- The diverging first-frequency HT loss eventually absorbs the complete
fixed scalar error budget. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMinorArcScalarError_le_firstOuter
    {X y : ℕ → ℕ} {α C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hC : 0 ≤ C) :
    ∀ᶠ n in atTop,
      (2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 2) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ) ≤
      smoothSaddleHildebrandTenenbaumLoss (X n) (y n)
          (1 / Real.log (y n : ℝ)) /
        (4 * smoothSaddleHTSharpComparisonConstant) := by
  let B := 1 + smoothSaddleHTPrimePowerNormalizedBound
  let K := smoothSaddleHTSharpComparisonConstant
  have hK : 0 < K := by
    dsimp [K]
    exact smoothSaddleHTSharpComparisonConstant_pos
  have hB : 0 ≤ B := by
    dsimp [B]
    linarith [smoothSaddleHTPrimePowerNormalizedBound_pos]
  have hloss :=
    (hregime.tendsto_smoothSaddleHTLoss_firstOuter_atTop hα).eventually
      (eventually_ge_atTop ((4 * K) * B))
  filter_upwards [hregime.eventually_htMinorArcScalarError_le_fixed hα hC,
    hloss] with n hscalar hloss
  rw [le_div_iff₀ (mul_pos (by norm_num) hK)]
  calc
    ((2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 2) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ)) *
          (4 * K) ≤ B * (4 * K) :=
      mul_le_mul_of_nonneg_right hscalar (by positivity)
    _ ≤ smoothSaddleHildebrandTenenbaumLoss (X n) (y n)
        (1 / Real.log (y n : ℝ)) := by
      simpa only [mul_comm] using hloss

/-- Radial monotonicity propagates first-frequency absorption across the
entire outer HT range. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMinorArcScalarError_le_loss
    {X y : ℕ → ℕ} {α C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      1 / Real.log (y n : ℝ) ≤ |t| →
      (2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 2) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ) ≤
      smoothSaddleHildebrandTenenbaumLoss (X n) (y n) t /
        (4 * smoothSaddleHTSharpComparisonConstant) := by
  filter_upwards
    [hregime.eventually_htMinorArcScalarError_le_firstOuter hα hC,
      hregime.eventually_two_le_X, hregime.eventually_two_le_y hα,
      (hregime.tendsto_log_y_atTop hα).eventually
        (eventually_gt_atTop (0 : ℝ))] with
      n hfirst hX hy hlogY
  intro t ht
  have hmono := smoothSaddleHildebrandTenenbaumLoss_mono hX hy
    (one_div_pos.mpr hlogY) ht
  rw [smoothSaddleHildebrandTenenbaumLoss_abs] at hmono
  exact hfirst.trans (div_le_div_of_nonneg_right hmono
    (mul_pos (by norm_num) smoothSaddleHTSharpComparisonConstant_pos).le)

/-- HT Lemma 8(ii) on its full outer frequency interval, now obtained
unconditionally in every Tao-critical smooth regime. -/
theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddleHTMinorArcBoundAt
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      SmoothSaddleHildebrandTenenbaumMinorArcBoundAt (X n) (y n)
        smoothSaddleHTMinorArcCoefficient
        (1 / Real.log (y n : ℝ))
        (smoothSaddleHTFrequencyCeiling (y n) (1 / 2)) := by
  obtain ⟨C, hHT⟩ := smoothSaddleHTMangoldtTransformEstimate
    (1 / 2) (by norm_num) (by norm_num)
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_htMinorArcScalarError_le_loss hα hHT.1.le] with
      n hX hy hsigmaHalf hsigmaOne herror
  apply hHT.minorArcBoundAt hX hy hsigmaHalf hsigmaOne le_rfl
  intro t htLower _htUpper
  exact herror t htLower

end

end Tao2026
