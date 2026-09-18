import Tao2026.SmoothNumberSaddleHTMinorArcScale

/-!
# The quarter-epsilon Hildebrand--Tenenbaum minor arc

The specialization `epsilon = 1/4` raises the available frequency ceiling
from `y` to `exp ((log y)^(5/4))`.  This file repeats only the scalar-error
absorption needed to access that larger interval; the analytic minor-arc
estimate itself remains the one proved from HT Lemma 6.
-/

namespace Tao2026

noncomputable section

open Filter Real
open scoped Topology

/-- The eighth power Rankin loss is absorbed by the weaker, but still
stretched-exponential, decay arising when `epsilon = 1/4`. -/
theorem IsTaoCriticalSmoothRegime.eventually_rankin_pow_eight_mul_ht_decay_quarter_le_one
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothRankinRatio (X n) (y n) ^ (8 : ℕ) *
          Real.exp (-(Real.log (y n : ℝ)) ^ (1 / 8 : ℝ)) ≤ 1 := by
  have hpoly0 :=
    eventually_const_mul_log_rpow_mul_exp_log_rpow_le_exp_log_rpow_of_lt
      (C := Real.exp (-1)) (α := 0) (β := (1 / 8 : ℝ))
      (by norm_num) (by norm_num) 8
  have hpoly := (hregime.tendsto_y_atTop hα).eventually hpoly0
  filter_upwards [hregime.eventually_rankinRatio_le_log_y hα, hpoly,
    hregime.eventually_two_le_X, hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ))] with n huL hpoly hX hy hL
  let u := smoothRankinRatio (X n) (y n)
  let L := Real.log (y n : ℝ)
  have huNonneg : 0 ≤ u := by
    dsimp [u]
    exact (smoothRankinRatio_pos hX hy).le
  rw [Real.rpow_natCast] at hpoly
  have hclean : L ^ (8 : ℕ) ≤ Real.exp (L ^ (1 / 8 : ℝ)) := by
    calc
      L ^ (8 : ℕ) = Real.exp (-1) * L ^ (8 : ℕ) * Real.exp 1 := by
        rw [show Real.exp (-1) * L ^ (8 : ℕ) * Real.exp 1 =
          L ^ (8 : ℕ) * (Real.exp (-1) * Real.exp 1) by ring,
          ← Real.exp_add]
        norm_num
      _ ≤ Real.exp (L ^ (1 / 8 : ℝ)) := by
        simpa only [L, Real.rpow_zero] using hpoly
  have hupow : u ^ (8 : ℕ) ≤ L ^ (8 : ℕ) := by
    exact pow_le_pow_left₀ huNonneg (by simpa only [u, L] using huL) 8
  calc
    u ^ (8 : ℕ) * Real.exp (-L ^ (1 / 8 : ℝ)) ≤
        Real.exp (L ^ (1 / 8 : ℝ)) *
          Real.exp (-L ^ (1 / 8 : ℝ)) := by
      gcongr
      exact hupow.trans hclean
    _ = 1 := by rw [← Real.exp_add]; simp

/-- At `epsilon = 1/4`, the normalized HT Lemma-6 error retains the same
explicit upper bound as in the half-epsilon specialization. -/
theorem smoothSaddleHTMangoldtError_quarter_div_log_le_four_div_log_rankin
    {X y : ℕ} (hy : 2 ≤ y)
    (hlogU : 0 < Real.log (smoothRankinRatio X y))
    (hsigmaOne : smoothSaddlePoint X y < 1)
    (hdecay : (y : ℝ) ^ (1 - smoothSaddlePoint X y) *
      Real.exp (-(Real.log (y : ℝ)) ^ (1 / 8 : ℝ)) ≤ 1)
    (hbetaLog : (1 / 2 : ℝ) * Real.log (smoothRankinRatio X y) ≤
      (1 - smoothSaddlePoint X y) * Real.log (y : ℝ)) :
    smoothSaddleHTMangoldtError y (1 - smoothSaddlePoint X y) (1 / 4) /
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
      1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 8 : ℝ)) := by
    positivity
  have hnumLe :
      1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 8 : ℝ)) ≤ 2 := by
    dsimp [beta, L] at hdecay ⊢
    linarith
  unfold smoothSaddleHTMangoldtError
  norm_num
  change (beta⁻¹ *
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 8 : ℝ)))) / L ≤
    4 / Real.log u
  rw [show (beta⁻¹ *
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 8 : ℝ)))) / L =
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 8 : ℝ))) /
        (beta * L) by field_simp]
  rw [div_le_div_iff₀ (mul_pos hbeta hL) hv]
  have hleft :
      (1 + (y : ℝ) ^ beta * Real.exp (-L ^ (1 / 8 : ℝ))) *
          Real.log u ≤ 2 * Real.log u :=
    mul_le_mul_of_nonneg_right hnumLe hv.le
  have hbetaLog' : (1 / 2 : ℝ) * Real.log u ≤ beta * L := by
    simpa only [u, beta, L] using hbetaLog
  nlinarith

/-- Critical-regime form of the quarter-epsilon Lemma-6 error estimate. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMangoldtError_quarter_div_log_le
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 4) /
            Real.log (y n : ℝ) ≤
        4 / Real.log (smoothRankinRatio (X n) (y n)) := by
  have hlogU : Tendsto
      (fun n => Real.log (smoothRankinRatio (X n) (y n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα,
    hregime.eventually_rankin_pow_eight_mul_ht_decay_quarter_le_one hα,
    hregime.eventually_half_log_rankin_le_displacement_mul_log hα,
    hlogU.eventually (eventually_gt_atTop (0 : ℝ))] with
      n hX hy hsigmaOne hdisp hpowDecay hbetaLog hlogU
  have hrpow := smoothSaddle_rpow_le_rankinRatio_pow_eight hX hy hdisp.le
  have hdecay : (y n : ℝ) ^
        (1 - smoothSaddlePoint (X n) (y n)) *
      Real.exp (-(Real.log (y n : ℝ)) ^ (1 / 8 : ℝ)) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le).trans hpowDecay
  exact smoothSaddleHTMangoldtError_quarter_div_log_le_four_div_log_rankin
    hy hlogU hsigmaOne hdecay hbetaLog

/-- The complete quarter-epsilon scalar error is eventually bounded by the
same fixed budget as the half-epsilon error. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMinorArcScalarError_quarter_le_fixed
    {X y : ℕ → ℕ} {α C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hC : 0 ≤ C) :
    ∀ᶠ n in atTop,
      (2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 4) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ) ≤
      1 + smoothSaddleHTPrimePowerNormalizedBound := by
  have hlogU : Tendsto
      (fun n => Real.log (smoothRankinRatio (X n) (y n))) atTop atTop :=
    Real.tendsto_log_atTop.comp (hregime.tendsto_rankinRatio_atTop hα)
  filter_upwards [hregime.eventually_htMangoldtError_quarter_div_log_le hα,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (1 : ℝ)),
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hlogU.eventually (eventually_gt_atTop (0 : ℝ)),
    hlogU.eventually (eventually_ge_atTop (8 * C))] with
      n herror hy hlogY hsigmaHalf hlogU hlogLarge
  let E := smoothSaddleHTMangoldtError (y n)
    (1 - smoothSaddlePoint (X n) (y n)) (1 / 4)
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

/-- The first outer-frequency loss absorbs the quarter-epsilon scalar
error budget. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMinorArcScalarError_quarter_le_firstOuter
    {X y : ℕ → ℕ} {α C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hC : 0 ≤ C) :
    ∀ᶠ n in atTop,
      (2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 4) +
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
  have hloss :=
    (hregime.tendsto_smoothSaddleHTLoss_firstOuter_atTop hα).eventually
      (eventually_ge_atTop ((4 * K) * B))
  filter_upwards
    [hregime.eventually_htMinorArcScalarError_quarter_le_fixed hα hC,
      hloss] with n hscalar hloss
  rw [le_div_iff₀ (mul_pos (by norm_num) hK)]
  calc
    ((2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 4) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ)) *
          (4 * K) ≤ B * (4 * K) :=
      mul_le_mul_of_nonneg_right hscalar (by positivity)
    _ ≤ smoothSaddleHildebrandTenenbaumLoss (X n) (y n)
        (1 / Real.log (y n : ℝ)) := by
      simpa only [mul_comm] using hloss

/-- Radial monotonicity propagates quarter-epsilon error absorption across
the entire enlarged outer range. -/
theorem IsTaoCriticalSmoothRegime.eventually_htMinorArcScalarError_quarter_le_loss
    {X y : ℕ → ℕ} {α C : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α)
    (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      1 / Real.log (y n : ℝ) ≤ |t| →
      (2 * C * smoothSaddleHTMangoldtError (y n)
          (1 - smoothSaddlePoint (X n) (y n)) (1 / 4) +
        2 * smoothSaddleHTPrimePowerRemainder (y n)
          (smoothSaddlePoint (X n) (y n))) / Real.log (y n : ℝ) ≤
      smoothSaddleHildebrandTenenbaumLoss (X n) (y n) t /
        (4 * smoothSaddleHTSharpComparisonConstant) := by
  filter_upwards
    [hregime.eventually_htMinorArcScalarError_quarter_le_firstOuter hα hC,
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

/-- HT Lemma 8(ii) through the enlarged quarter-epsilon frequency ceiling. -/
theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddleHTMinorArcBoundAt_quarter
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop,
      SmoothSaddleHildebrandTenenbaumMinorArcBoundAt (X n) (y n)
        smoothSaddleHTMinorArcCoefficient
        (1 / Real.log (y n : ℝ))
        (smoothSaddleHTFrequencyCeiling (y n) (1 / 4)) := by
  obtain ⟨C, hHT⟩ := smoothSaddleHTMangoldtTransformEstimate
    (1 / 4) (by norm_num) (by norm_num)
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ici_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
    hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_htMinorArcScalarError_quarter_le_loss hα hHT.1.le] with
      n hX hy hsigmaHalf hsigmaOne herror
  apply hHT.minorArcBoundAt hX hy hsigmaHalf hsigmaOne le_rfl
  intro t htLower _htUpper
  exact herror t htLower

end

end Tao2026
