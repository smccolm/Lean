import Tao2026.SmoothNumberSaddleFourthShell

/-!
# Vanishing of the normalized fourth outer Perron shell

The eighth-root alphabet gives a loss of order `u^(1/9) / log u`.  Its
exponential absorbs the square-root saddle normalization, making the exact
symmetric contribution from `6*pi/log y` through `12*pi/log y` vanish.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

theorem rankinRatio_rpow_one_ninth_le_fourthPrimeScale_rpow
    {X y : ℕ} (hX : 2 ≤ X) (hy : 256 ≤ y)
    (hlogY : 126 * Real.log 2 ≤ Real.log (y : ℝ))
    (hlogYOne : 1 ≤ Real.log (y : ℝ))
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1) :
    (smoothRankinRatio X y / (15 * Real.log 4)) ^ (1 / 9 : ℝ) ≤
      (smoothSaddleFourthPrimeScale y : ℝ) ^
        (1 - smoothSaddlePoint X y) := by
  let u := smoothRankinRatio X y
  let sigma := smoothSaddlePoint X y
  let N := smoothSaddleFourthPrimeScale y
  let e := 1 - sigma
  have he : 0 ≤ e := by dsimp only [e, sigma]; linarith
  have hyPos : (0 : ℝ) < y := by positivity
  have hN : 2 ≤ N := by
    dsimp only [N]
    exact two_le_smoothSaddleFourthPrimeScale hy
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have huPos : 0 < u := by
    dsimp only [u]
    exact smoothRankinRatio_pos hX (by omega)
  have hCPos : 0 < 15 * Real.log 4 := by positivity
  have hbase : u / (15 * Real.log 4) ≤ (y : ℝ) ^ e := by
    simpa only [u, sigma, e] using
      rankinRatio_div_fifteen_log_four_le_saddle_rpow
        hX (by omega) hlogYOne hsigmaHalf hsigmaOne
  have hraise : (u / (15 * Real.log 4)) ^ (1 / 9 : ℝ) ≤
      ((y : ℝ) ^ e) ^ (1 / 9 : ℝ) :=
    Real.rpow_le_rpow (div_nonneg huPos.le hCPos.le) hbase (by norm_num)
  have hlogN : (1 / 9 : ℝ) * Real.log (y : ℝ) ≤ Real.log (N : ℝ) := by
    simpa only [N] using
      one_ninth_log_le_log_smoothSaddleFourthPrimeScale hy hlogY
  have hexponent : (1 / 9 : ℝ) * e * Real.log (y : ℝ) ≤
      e * Real.log (N : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlogN he
    nlinarith
  calc
    (u / (15 * Real.log 4)) ^ (1 / 9 : ℝ) ≤
        ((y : ℝ) ^ e) ^ (1 / 9 : ℝ) := hraise
    _ = (y : ℝ) ^ (e * (1 / 9 : ℝ)) := by rw [Real.rpow_mul hyPos.le]
    _ ≤ (N : ℝ) ^ e := by
      rw [Real.rpow_def_of_pos hyPos, Real.rpow_def_of_pos hNPos]
      apply Real.exp_le_exp.mpr
      nlinarith

theorem fourthOuterMultiShell_cosineLoss_lower_at_saddle
    {B X y : ℕ} {t : ℝ} (hB : 4 ≤ B) (hX : 2 ≤ X) (hy : 256 ≤ y)
    (hlogY : 126 * Real.log 2 ≤ Real.log (y : ℝ))
    (hlogYOne : 1 ≤ Real.log (y : ℝ))
    (hlogU : 12 ≤ Real.log (smoothRankinRatio X y))
    (hBu : (B : ℝ) ≤ smoothRankinRatio X y)
    (huN : smoothRankinRatio X y ≤
      Real.sqrt (smoothSaddleFourthPrimeScale y))
    (hpnt : ∀ n : ℕ, B ≤ n →
      (3 / 4 : ℝ) * n ≤ Chebyshev.theta (n : ℝ) ∧
        Chebyshev.theta (n : ℝ) ≤ (5 / 4 : ℝ) * n)
    (hsigmaHalf : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y)
    (hsigmaOne : smoothSaddlePoint X y ≤ 1)
    (hdisplacement : 1 - smoothSaddlePoint X y ≤
      8 * Real.log (smoothRankinRatio X y) / Real.log (y : ℝ))
    (htLower : 6 * Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 12 * Real.pi / Real.log (y : ℝ)) :
    (Real.exp (-16) *
        (smoothRankinRatio X y / (15 * Real.log 4)) ^ (1 / 9 : ℝ)) /
        (16 * Real.log 2 * Real.log (smoothRankinRatio X y)) ≤
      smoothSaddleCosineLoss y (smoothSaddlePoint X y) t := by
  let u := smoothRankinRatio X y
  let sigma := smoothSaddlePoint X y
  let N := smoothSaddleFourthPrimeScale y
  let w := cepDyadicCofactorCutoff N u
  have hN : 2 ≤ N := two_le_smoothSaddleFourthPrimeScale hy
  have hlogyPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogNPos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogNUpper := log_smoothSaddleFourthPrimeScale_le_eighth_log hy
  have hlogNLeY : Real.log (N : ℝ) ≤ Real.log (y : ℝ) := by
    calc
      Real.log (N : ℝ) ≤ (1 / 8 : ℝ) * Real.log (y : ℝ) := by
        simpa only [N] using hlogNUpper
      _ ≤ Real.log (y : ℝ) := by
        have := hlogyPos.le
        nlinarith
  have he : 0 ≤ 1 - sigma := by dsimp only [sigma]; linarith
  have hdispMul : (1 - sigma) * Real.log (y : ℝ) ≤ 8 * Real.log u := by
    apply (le_div_iff₀ hlogyPos).mp
    simpa only [u, sigma] using hdisplacement
  have hdispN : 1 - sigma ≤ 8 * Real.log u / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlogNPos).mpr
    calc
      (1 - sigma) * Real.log (N : ℝ) ≤
          (1 - sigma) * Real.log (y : ℝ) :=
        mul_le_mul_of_nonneg_left hlogNLeY he
      _ ≤ 8 * Real.log u := hdispMul
  have hrankin := rankinRatio_rpow_one_ninth_le_fourthPrimeScale_rpow
    hX hy hlogY hlogYOne hsigmaHalf hsigmaOne
  have hcofactor := exp_neg_sixteen_mul_rpow_le_cofactor_rpow
    hB hN (by linarith) hBu huN hsigmaOne hdispN
  have hmulti := fourthOuterMultiShell_cosineLoss_lower
    hB hy hlogY hlogU hBu huN hpnt hsigmaOne htLower htUpper
  have hleft : Real.exp (-16) *
      (u / (15 * Real.log 4)) ^ (1 / 9 : ℝ) ≤
      (w : ℝ) ^ (1 - sigma) := by
    calc
      Real.exp (-16) * (u / (15 * Real.log 4)) ^ (1 / 9 : ℝ) ≤
          Real.exp (-16) * (N : ℝ) ^ (1 - sigma) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [u, sigma, N] using hrankin) (Real.exp_pos _).le
      _ ≤ (w : ℝ) ^ (1 - sigma) := by
        simpa only [u, sigma, N, w] using hcofactor
  have hden : 0 < 16 * Real.log 2 * Real.log u := by
    have : 0 < Real.log u := by dsimp only [u]; linarith
    positivity
  calc
    (Real.exp (-16) *
        (smoothRankinRatio X y / (15 * Real.log 4)) ^ (1 / 9 : ℝ)) /
        (16 * Real.log 2 * Real.log (smoothRankinRatio X y)) =
      (Real.exp (-16) * (u / (15 * Real.log 4)) ^ (1 / 9 : ℝ)) /
        (16 * Real.log 2 * Real.log u) := by rfl
    _ ≤ (w : ℝ) ^ (1 - sigma) /
        (16 * Real.log 2 * Real.log u) :=
      div_le_div_of_nonneg_right hleft hden.le
    _ ≤ smoothSaddleCosineLoss y sigma t := by
      simpa only [u, sigma, N, w] using hmulti

noncomputable def smoothSaddleFourthOuterLossScale (X y : ℕ) : ℝ :=
  (Real.exp (-16) *
      (smoothRankinRatio X y / (15 * Real.log 4)) ^ (1 / 9 : ℝ)) /
    (16 * Real.log 2 * Real.log (smoothRankinRatio X y))

theorem tendsto_rpow_one_ninth_div_log_atTop
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) :
    Tendsto (fun n => (u n) ^ (1 / 9 : ℝ) / Real.log (u n))
      atTop atTop := by
  have hpow : Tendsto (fun n => (u n) ^ (1 / 18 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 18)).comp hu
  have hlogSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 18)).def (by norm_num : (0 : ℝ) < 1)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [hu.eventually hlogSmall,
    hu.eventually (eventually_gt_atTop (1 : ℝ))] with n hlog huOne
  have huPos : 0 < u n := lt_trans zero_lt_one huOne
  have hlogPos : 0 < Real.log (u n) := Real.log_pos huOne
  have hpowPos : 0 < (u n) ^ (1 / 18 : ℝ) := Real.rpow_pos_of_pos huPos _
  have hlogLe : Real.log (u n) ≤ (u n) ^ (1 / 18 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogPos,
      abs_of_pos hpowPos, one_mul] using hlog
  rw [le_div_iff₀ hlogPos]
  calc
    (u n) ^ (1 / 18 : ℝ) * Real.log (u n) ≤
        (u n) ^ (1 / 18 : ℝ) * (u n) ^ (1 / 18 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogLe hpowPos.le
    _ = (u n) ^ (1 / 9 : ℝ) := by
      rw [← Real.rpow_add huPos]
      congr 1
      ring

theorem tendsto_sqrt_mul_exp_neg_rpow_one_ninth_div_log_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.sqrt (u n) *
      Real.exp (-a * ((u n) ^ (1 / 9 : ℝ) / Real.log (u n))))
      atTop (𝓝 0) := by
  have hroot : Tendsto (fun n => (u n) ^ (1 / 18 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 18)).comp hu
  have hupper : Tendsto (fun n =>
      ((u n) ^ (1 / 18 : ℝ)) ^ (9 : ℝ) *
        Real.exp (-a * (u n) ^ (1 / 18 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 9 a ha).comp hroot
  have hlogSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 18)).def (by norm_num : (0 : ℝ) < 1)
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
    (Real.sqrt_nonneg _) (Real.exp_pos _).le) ?_ hupper
  filter_upwards [hu.eventually hlogSmall,
    hu.eventually (eventually_gt_atTop (1 : ℝ))] with n hlog huOne
  have huPos : 0 < u n := lt_trans zero_lt_one huOne
  have hlogPos : 0 < Real.log (u n) := Real.log_pos huOne
  have hrootPos : 0 < (u n) ^ (1 / 18 : ℝ) := Real.rpow_pos_of_pos huPos _
  have hlogLe : Real.log (u n) ≤ (u n) ^ (1 / 18 : ℝ) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogPos,
      abs_of_pos hrootPos, one_mul] using hlog
  have hratio : (u n) ^ (1 / 18 : ℝ) ≤
      (u n) ^ (1 / 9 : ℝ) / Real.log (u n) := by
    rw [le_div_iff₀ hlogPos]
    calc
      (u n) ^ (1 / 18 : ℝ) * Real.log (u n) ≤
          (u n) ^ (1 / 18 : ℝ) * (u n) ^ (1 / 18 : ℝ) :=
        mul_le_mul_of_nonneg_left hlogLe hrootPos.le
      _ = (u n) ^ (1 / 9 : ℝ) := by
        rw [← Real.rpow_add huPos]
        congr 1
        ring
  have hsqrt : ((u n) ^ (1 / 18 : ℝ)) ^ (9 : ℝ) = Real.sqrt (u n) := by
    rw [← Real.rpow_mul huPos.le]
    norm_num
    rw [← Real.sqrt_eq_rpow]
  have hexp : Real.exp (-a * ((u n) ^ (1 / 9 : ℝ) / Real.log (u n))) ≤
      Real.exp (-a * (u n) ^ (1 / 18 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [hsqrt]
  exact mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleFourthOuterLossScale_atTop
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleFourthOuterLossScale (X n) (y n))
      atTop atTop := by
  let C : ℝ := 15 * Real.log 4
  let K : ℝ := Real.exp (-16) /
    (C ^ (1 / 9 : ℝ) * (16 * Real.log 2))
  have hC : 0 < C := by dsimp only [C]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hbase := tendsto_rpow_one_ninth_div_log_atTop
    (hregime.tendsto_rankinRatio_atTop hα)
  have hscaled := hbase.const_mul_atTop hK
  apply hscaled.congr'
  filter_upwards [(hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_gt_atTop (1 : ℝ))] with n hu
  have huPos : 0 < smoothRankinRatio (X n) (y n) := lt_trans zero_lt_one hu
  have hlogu : Real.log (smoothRankinRatio (X n) (y n)) ≠ 0 :=
    (Real.log_pos hu).ne'
  unfold smoothSaddleFourthOuterLossScale
  dsimp only [K, C]
  rw [Real.div_rpow huPos.le hC.le]
  field_simp [hlogu, hC.ne',
    (Real.rpow_pos_of_pos hC (1 / 9 : ℝ)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

theorem IsTaoCriticalSmoothRegime.tendsto_sqrt_rankinRatio_mul_fourthOuterEnvelope_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      Real.sqrt (smoothRankinRatio (X n) (y n)) *
        Real.exp (-(smoothSaddleFourthOuterLossScale (X n) (y n) / 96)))
      atTop (𝓝 0) := by
  let C : ℝ := 15 * Real.log 4
  let a : ℝ := Real.exp (-16) /
    (C ^ (1 / 9 : ℝ) * (16 * Real.log 2) * 96)
  have hC : 0 < C := by dsimp only [C]; positivity
  have ha : 0 < a := by dsimp only [a]; positivity
  have h := tendsto_sqrt_mul_exp_neg_rpow_one_ninth_div_log_zero
    (hregime.tendsto_rankinRatio_atTop hα) ha
  apply h.congr'
  filter_upwards [(hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_gt_atTop (1 : ℝ))] with n hu
  have huPos : 0 < smoothRankinRatio (X n) (y n) := lt_trans zero_lt_one hu
  have hlogu : Real.log (smoothRankinRatio (X n) (y n)) ≠ 0 :=
    (Real.log_pos hu).ne'
  congr 1
  apply congrArg Real.exp
  unfold smoothSaddleFourthOuterLossScale
  dsimp only [a, C]
  rw [Real.div_rpow huPos.le hC.le]
  field_simp [hlogu, hC.ne',
    (Real.rpow_pos_of_pos hC (1 / 9 : ℝ)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

theorem IsTaoCriticalSmoothRegime.eventually_smoothSaddleFourthOuterLossScale_le_cosineLoss
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      6 * Real.pi / Real.log (y n : ℝ) ≤ t →
      t ≤ 12 * Real.pi / Real.log (y n : ℝ) →
      smoothSaddleFourthOuterLossScale (X n) (y n) ≤
        smoothSaddleCosineLoss (y n) (smoothSaddlePoint (X n) (y n)) t := by
  obtain ⟨B, hB, hpnt⟩ := exists_chebyshevTheta_quarter_threshold
  have huTop := hregime.tendsto_rankinRatio_atTop hα
  have hloguTop := Real.tendsto_log_atTop.comp huTop
  have hsaddleHalf := (hregime.tendsto_smoothSaddlePoint_one hα).eventually
    (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hregime.eventually_two_le_X,
    (hregime.tendsto_y_atTop hα).eventually (eventually_ge_atTop 256),
    (hregime.tendsto_log_y_atTop hα).eventually
      (eventually_ge_atTop (126 * Real.log 2)),
    (hregime.tendsto_log_y_atTop hα).eventually (eventually_ge_atTop (1 : ℝ)),
    hloguTop.eventually (eventually_ge_atTop (12 : ℝ)),
    huTop.eventually (eventually_ge_atTop (B : ℝ)),
    hregime.eventually_rankinRatio_le_sqrt_fourthPrimeScale hα,
    hsaddleHalf, hregime.eventually_smoothSaddlePoint_lt_one hα,
    hregime.eventually_one_sub_saddle_lt_eight_log_ratio hα] with
      n hX hy hlogY hlogYOne hlogU hBu huN hsigmaHalf hsigmaOne hdisp
  intro t htLower htUpper
  unfold smoothSaddleFourthOuterLossScale
  exact fourthOuterMultiShell_cosineLoss_lower_at_saddle
    hB hX hy hlogY hlogYOne hlogU hBu huN hpnt hsigmaHalf.le
    hsigmaOne.le hdisp.le htLower htUpper

noncomputable def smoothSaddleFourthOuterUpperHeight (y : ℕ) : ℝ :=
  12 * Real.pi / Real.log (y : ℝ)

noncomputable def smoothSaddleFourthOuterPerronContribution
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleThirdOuterUpperHeight y)
    (smoothSaddleFourthOuterUpperHeight y)

theorem IsTaoCriticalSmoothRegime.eventually_norm_smoothSaddlePerronLineIntegrand_le_fourthOuterEnvelope_abs
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      smoothSaddleThirdOuterUpperHeight (y n) ≤ |t| →
      |t| ≤ smoothSaddleFourthOuterUpperHeight (y n) →
      ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleFourthOuterLossScale (X n) (y n) / 96)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_smoothSaddleFourthOuterLossScale_le_cosineLoss hα] with
      n hX hy hsigma hloss
  intro t htLower htUpper
  have hlossT : smoothSaddleFourthOuterLossScale (X n) (y n) ≤
      smoothSaddleCosineLoss (y n) (smoothSaddlePoint (X n) (y n)) t := by
    by_cases ht : 0 ≤ t
    · have habs : |t| = t := abs_of_nonneg ht
      exact hloss t
        (by simpa [smoothSaddleThirdOuterUpperHeight, habs] using htLower)
        (by simpa [smoothSaddleFourthOuterUpperHeight, habs] using htUpper)
    · have habs : |t| = -t := abs_of_neg (lt_of_not_ge ht)
      have h := hloss (-t)
        (by simpa [smoothSaddleThirdOuterUpperHeight, habs] using htLower)
        (by simpa [smoothSaddleFourthOuterUpperHeight, habs] using htUpper)
      rw [smoothSaddleCosineLoss_neg] at h
      exact h
  calc
    ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t / 96)) :=
      norm_smoothSaddlePerronLineIntegrand_le_cosineLoss hX hy hsigma.le t
    _ ≤ Real.exp (-(smoothSaddleFourthOuterLossScale (X n) (y n) / 96)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleFourthOuterPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n => smoothSaddleFourthOuterPerronContribution (X n) (y n))
      atTop (𝓝 0) := by
  let C : ℝ := 12 * Real.pi * Real.sqrt 7 / Real.sqrt (2 * Real.pi)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdecay := hregime.tendsto_sqrt_rankinRatio_mul_fourthOuterEnvelope_zero hα
  have hupper : Tendsto (fun n => C *
      (Real.sqrt (smoothRankinRatio (X n) (y n)) *
        Real.exp (-(smoothSaddleFourthOuterLossScale (X n) (y n) / 96))))
      atTop (𝓝 0) := by
    simpa using hdecay.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
  filter_upwards [hregime.eventually_two_le_X, hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_norm_smoothSaddlePerronLineIntegrand_le_fourthOuterEnvelope_abs hα]
    with n hX hy hsigma hpoint
  let E := Real.exp (-(smoothSaddleFourthOuterLossScale (X n) (y n) / 96))
  let L := smoothSaddleThirdOuterUpperHeight (y n)
  let U := smoothSaddleFourthOuterUpperHeight (y n)
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hL : 0 ≤ L := by
    dsimp only [L, smoothSaddleThirdOuterUpperHeight]
    positivity
  have hLU : L ≤ U := by
    dsimp only [L, U, smoothSaddleThirdOuterUpperHeight,
      smoothSaddleFourthOuterUpperHeight]
    apply (div_le_div_iff₀ hlogy hlogy).mpr
    nlinarith [Real.pi_pos]
  have hnorm := norm_smoothSaddleSymmetricPerronShellContribution_le
    hX hy hL hLU (E := E) hpoint
  have hwidth : U - L = 6 * Real.pi / Real.log (y n : ℝ) := by
    dsimp only [U, L, smoothSaddleFourthOuterUpperHeight,
      smoothSaddleThirdOuterUpperHeight]
    field_simp [hlogy.ne']
    ring
  have hsd := smoothSaddleStandardDeviation_div_log_le_sqrt_rankinRatio
    hX hy hsigma.le
  have hsqrtMul : Real.sqrt (7 * smoothRankinRatio (X n) (y n)) =
      Real.sqrt 7 * Real.sqrt (smoothRankinRatio (X n) (y n)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7)]
  change ‖smoothSaddleSymmetricPerronShellContribution (X n) (y n) L U‖ ≤ _
  rw [hwidth] at hnorm
  calc
    ‖smoothSaddleSymmetricPerronShellContribution (X n) (y n) L U‖ ≤
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
          (2 * E * (6 * Real.pi / Real.log (y n : ℝ))) := hnorm
    _ = (12 * Real.pi / Real.sqrt (2 * Real.pi)) *
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.log (y n : ℝ) * E) := by
      field_simp [hlogy.ne', (Real.sqrt_pos.2 (by positivity :
        (0 : ℝ) < 2 * Real.pi)).ne']
      ring
    _ ≤ (12 * Real.pi / Real.sqrt (2 * Real.pi)) *
        (Real.sqrt (7 * smoothRankinRatio (X n) (y n)) * E) := by
      gcongr
    _ = C * (Real.sqrt (smoothRankinRatio (X n) (y n)) * E) := by
      rw [hsqrtMul]
      dsimp only [C]
      ring

end

end Tao2026
