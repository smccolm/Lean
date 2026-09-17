import Tao2026.SmoothNumberSaddleMultiShell

/-!
# Vanishing of the normalized first outer Perron shell

This module integrates the accumulated loss from the first outer-frequency
shell.  It defines the exact symmetric physical contribution, bounds both
interval integrals by the release-3.93 envelope, and uses the curvature upper
bound `standardDeviation / log y <= sqrt (7*u)`.  Exponential decay of order
`exp (-c*u/log u)` absorbs that square-root normalization, proving that the
normalized first-shell contribution tends to zero in every critical regime.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

theorem tendsto_sqrt_mul_exp_neg_self_div_log_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => Real.sqrt (u n) *
      Real.exp (-a * (u n / Real.log (u n)))) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (u n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hu
  have hupper : Tendsto (fun n =>
      (Real.sqrt (u n)) ^ (1 : ℝ) * Real.exp (-a * Real.sqrt (u n)))
      atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha).comp hsqrt
  have hlogSmall := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 2)).def (by norm_num : (0 : ℝ) < 1)
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
    (Real.sqrt_nonneg _) (Real.exp_pos _).le) ?_ hupper
  filter_upwards [hu.eventually hlogSmall,
    hu.eventually (eventually_ge_atTop (2 : ℝ))] with n hlog huTwo
  have huPos : 0 < u n := by linarith
  have huOne : 1 ≤ u n := by linarith
  have hlogPos : 0 < Real.log (u n) := Real.log_pos (by linarith)
  have hsqrtPos : 0 < Real.sqrt (u n) := Real.sqrt_pos.2 huPos
  have hsqrtPow : (u n) ^ (1 / 2 : ℝ) = Real.sqrt (u n) := by
    rw [Real.sqrt_eq_rpow]
  have hlogLe : Real.log (u n) ≤ Real.sqrt (u n) := by
    rw [← hsqrtPow]
    simpa only [Real.norm_eq_abs, abs_of_pos hlogPos,
      abs_of_pos (Real.rpow_pos_of_pos huPos _), one_mul] using hlog
  have hratio : Real.sqrt (u n) ≤ u n / Real.log (u n) := by
    rw [le_div_iff₀ hlogPos]
    calc
      Real.sqrt (u n) * Real.log (u n) ≤
          Real.sqrt (u n) * Real.sqrt (u n) :=
        mul_le_mul_of_nonneg_left hlogLe (Real.sqrt_nonneg _)
      _ = u n := Real.mul_self_sqrt huPos.le
  have hexp : Real.exp (-a * (u n / Real.log (u n))) ≤
      Real.exp (-a * Real.sqrt (u n)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simpa only [Real.rpow_one] using
    mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)

noncomputable def smoothSaddleFirstOuterUpperHeight (y : ℕ) : ℝ :=
  4 * Real.pi / (3 * Real.log (y : ℝ))

noncomputable def smoothSaddleFirstOuterPerronContribution
    (X y : ℕ) : ℂ :=
  ((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-smoothSaddleFirstOuterUpperHeight y)..
          (-smoothSaddleWidePerronHeight X y),
        smoothSaddlePerronLineIntegrand X y t) +
      ∫ t in (smoothSaddleWidePerronHeight X y)..
          (smoothSaddleFirstOuterUpperHeight y),
        smoothSaddlePerronLineIntegrand X y t)

theorem norm_smoothSaddleFirstOuterPerronContribution_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y) {E : ℝ}
    (hpoint : ∀ t : ℝ,
      smoothSaddleWidePerronHeight X y ≤ |t| →
      |t| ≤ smoothSaddleFirstOuterUpperHeight y →
      ‖smoothSaddlePerronLineIntegrand X y t‖ ≤ E) :
    ‖smoothSaddleFirstOuterPerronContribution X y‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * E * (smoothSaddleFirstOuterUpperHeight y -
          smoothSaddleWidePerronHeight X y)) := by
  let H := smoothSaddleWidePerronHeight X y
  let U := smoothSaddleFirstOuterUpperHeight y
  let f := smoothSaddlePerronLineIntegrand X y
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hH : 0 < H := by
    dsimp only [H]
    rw [smoothSaddleWidePerronHeight_eq_pi_div_log hX hy]
    positivity
  have hHU : H ≤ U := by
    dsimp only [H, U]
    rw [smoothSaddleWidePerronHeight_eq_pi_div_log hX hy,
      smoothSaddleFirstOuterUpperHeight]
    apply (div_le_div_iff₀ hlog (mul_pos (by norm_num) hlog)).mpr
    nlinarith [Real.pi_pos]
  have hleft : ‖∫ t in (-U)..(-H), f t‖ ≤ E * (U - H) := by
    calc
      ‖∫ t in (-U)..(-H), f t‖ ≤ E * |(-H) - (-U)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le (by linarith : -U ≤ -H)] at ht
        apply hpoint t
        · rw [abs_of_nonpos (by linarith [ht.2, hH] : t ≤ 0)]
          linarith [ht.2]
        · rw [abs_of_nonpos (by linarith [ht.2, hH] : t ≤ 0)]
          linarith [ht.1]
      _ = E * (U - H) := by
        congr 1
        rw [show -H - -U = U - H by ring,
          abs_of_nonneg (sub_nonneg.mpr hHU)]
  have hright : ‖∫ t in H..U, f t‖ ≤ E * (U - H) := by
    calc
      ‖∫ t in H..U, f t‖ ≤ E * |U - H| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le hHU] at ht
        apply hpoint t
        · rw [abs_of_nonneg (by linarith [ht.1, hH] : 0 ≤ t)]
          exact ht.1.le
        · rw [abs_of_nonneg (by linarith [ht.1, hH] : 0 ≤ t)]
          exact ht.2
      _ = E * (U - H) := by rw [abs_of_nonneg (sub_nonneg.mpr hHU)]
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  unfold smoothSaddleFirstOuterPerronContribution
  change ‖((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-U)..(-H), f t) + ∫ t in H..U, f t)‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * E * (U - H))
  rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hsd.le, Real.norm_of_nonneg hsqrt.le]
  calc
    smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi) *
        ‖(∫ t in (-U)..(-H), f t) + ∫ t in H..U, f t‖ ≤
      smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi) *
        (‖∫ t in (-U)..(-H), f t‖ + ‖∫ t in H..U, f t‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi) *
        (2 * E * (U - H)) := by
      gcongr
      linarith
    _ = _ := by rfl

theorem IsTaoCriticalSmoothRegime.eventually_norm_smoothSaddlePerronLineIntegrand_le_firstOuterEnvelope_abs
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      smoothSaddleWidePerronHeight (X n) (y n) ≤ |t| →
      |t| ≤ smoothSaddleFirstOuterUpperHeight (y n) →
      ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_smoothSaddleFirstOuterLossScale_le_cosineLoss hα] with
      n hX hy hsigma hloss
  intro t htLower htUpper
  have hH := smoothSaddleWidePerronHeight_eq_pi_div_log hX hy
  have hU : smoothSaddleFirstOuterUpperHeight (y n) =
      4 * Real.pi / (3 * Real.log (y n : ℝ)) := rfl
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hUpperCompare : 4 * Real.pi / (3 * Real.log (y n : ℝ)) ≤
      3 * Real.pi / (2 * Real.log (y n : ℝ)) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlogy)
      (mul_pos (by norm_num) hlogy)).mpr
    nlinarith [Real.pi_pos]
  have hlossT : smoothSaddleFirstOuterLossScale (X n) (y n) ≤
      smoothSaddleCosineLoss (y n) (smoothSaddlePoint (X n) (y n)) t := by
    by_cases ht : 0 ≤ t
    · have habs : |t| = t := abs_of_nonneg ht
      have htOld : t ≤ 4 * Real.pi / (3 * Real.log (y n : ℝ)) := by
        simpa [hU, habs] using htUpper
      exact hloss t (by simpa [hH, habs] using htLower)
        (htOld.trans hUpperCompare)
    · have habs : |t| = -t := abs_of_neg (lt_of_not_ge ht)
      have htOld : -t ≤ 4 * Real.pi / (3 * Real.log (y n : ℝ)) := by
        simpa [hU, habs] using htUpper
      have h := hloss (-t) (by simpa [hH, habs] using htLower)
        (htOld.trans hUpperCompare)
      rw [smoothSaddleCosineLoss_neg] at h
      exact h
  calc
    ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t / 96)) :=
      norm_smoothSaddlePerronLineIntegrand_le_cosineLoss hX hy hsigma.le t
    _ ≤ Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

theorem IsTaoCriticalSmoothRegime.tendsto_sqrt_rankinRatio_mul_firstOuterEnvelope_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      Real.sqrt (smoothRankinRatio (X n) (y n)) *
        Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)))
      atTop (𝓝 0) := by
  let a : ℝ := Real.exp (-16) /
    (15 * Real.log 4 * (16 * Real.log 2) * 96)
  have ha : 0 < a := by dsimp only [a]; positivity
  have h := tendsto_sqrt_mul_exp_neg_self_div_log_zero
    (hregime.tendsto_rankinRatio_atTop hα) ha
  apply h.congr'
  filter_upwards [(hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_gt_atTop (1 : ℝ))] with n hu
  have hlogu : Real.log (smoothRankinRatio (X n) (y n)) ≠ 0 :=
    (Real.log_pos hu).ne'
  congr 1
  apply congrArg Real.exp
  unfold smoothSaddleFirstOuterLossScale
  dsimp only [a]
  field_simp [hlogu, (Real.log_pos (by norm_num : (1 : ℝ) < 4)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

theorem smoothSaddleStandardDeviation_div_log_le_sqrt_rankinRatio
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    (hsigma : (1 / 2 : ℝ) ≤ smoothSaddlePoint X y) :
    smoothSaddleStandardDeviation X y / Real.log (y : ℝ) ≤
      Real.sqrt (7 * smoothRankinRatio X y) := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hu : 0 < smoothRankinRatio X y := smoothRankinRatio_pos hX hy
  have hphi0 : 0 ≤
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) :=
    (smoothSaddlePhiTwo_pos hy (smoothSaddlePoint_pos hX hy)).le
  have hphi := smoothSaddlePhiTwo_saddle_le_seven_log_mul_log
    hX hy hsigma
  have hlogX : smoothRankinRatio X y * Real.log (y : ℝ) =
      Real.log (X : ℝ) := smoothRankinRatio_mul_log hy
  have hphi' : smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
      7 * smoothRankinRatio X y * Real.log (y : ℝ) ^ 2 := by
    calc
      smoothSaddlePhiTwo y (smoothSaddlePoint X y) ≤
          7 * Real.log (y : ℝ) * Real.log (X : ℝ) := hphi
      _ = 7 * smoothRankinRatio X y * Real.log (y : ℝ) ^ 2 := by
        rw [← hlogX]
        ring
  have hleft0 : 0 ≤ smoothSaddleStandardDeviation X y /
      Real.log (y : ℝ) := div_nonneg
        (smoothSaddleStandardDeviation_pos hX hy).le hlogy.le
  have hright0 : 0 ≤ 7 * smoothRankinRatio X y :=
    mul_nonneg (by norm_num) hu.le
  apply (Real.le_sqrt hleft0 hright0).2
  unfold smoothSaddleStandardDeviation
  rw [div_pow, Real.sq_sqrt hphi0]
  apply (div_le_iff₀ (sq_pos_of_pos hlogy)).mpr
  nlinarith

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleFirstOuterPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleFirstOuterPerronContribution (X n) (y n))
      atTop (𝓝 0) := by
  let C : ℝ :=
    (2 * Real.pi * Real.sqrt 7) / (3 * Real.sqrt (2 * Real.pi))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdecay :=
    hregime.tendsto_sqrt_rankinRatio_mul_firstOuterEnvelope_zero hα
  have hupper : Tendsto (fun n => C *
      (Real.sqrt (smoothRankinRatio (X n) (y n)) *
        Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96))))
      atTop (𝓝 0) := by
    simpa using hdecay.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_norm_smoothSaddlePerronLineIntegrand_le_firstOuterEnvelope_abs hα]
    with n hX hy hsigma hpoint
  let E := Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96))
  have hnorm := norm_smoothSaddleFirstOuterPerronContribution_le
    hX hy (E := E) hpoint
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hwidth : smoothSaddleFirstOuterUpperHeight (y n) -
      smoothSaddleWidePerronHeight (X n) (y n) =
        Real.pi / (3 * Real.log (y n : ℝ)) := by
    rw [smoothSaddleFirstOuterUpperHeight,
      smoothSaddleWidePerronHeight_eq_pi_div_log hX hy]
    field_simp [hlogy.ne']
    ring
  have hsd := smoothSaddleStandardDeviation_div_log_le_sqrt_rankinRatio
    hX hy hsigma.le
  have hsqrtMul : Real.sqrt (7 * smoothRankinRatio (X n) (y n)) =
      Real.sqrt 7 * Real.sqrt (smoothRankinRatio (X n) (y n)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7)]
  rw [hwidth] at hnorm
  calc
    ‖smoothSaddleFirstOuterPerronContribution (X n) (y n)‖ ≤
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
          (2 * E * (Real.pi / (3 * Real.log (y n : ℝ)))) := hnorm
    _ = (2 * Real.pi / (3 * Real.sqrt (2 * Real.pi))) *
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.log (y n : ℝ) * E) := by
      field_simp [hlogy.ne', (Real.sqrt_pos.2 (by positivity :
        (0 : ℝ) < 2 * Real.pi)).ne']
    _ ≤ (2 * Real.pi / (3 * Real.sqrt (2 * Real.pi))) *
        (Real.sqrt (7 * smoothRankinRatio (X n) (y n)) * E) := by
      gcongr
    _ = C * (Real.sqrt (smoothRankinRatio (X n) (y n)) * E) := by
      rw [hsqrtMul]
      dsimp only [C]
      ring

end

end Tao2026
