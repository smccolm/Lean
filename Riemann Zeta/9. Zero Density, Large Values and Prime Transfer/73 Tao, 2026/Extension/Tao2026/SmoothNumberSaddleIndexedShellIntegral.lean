import Tao2026.SmoothNumberSaddleIndexedLossScale

/-!
# Vanishing of every fixed indexed outer shell

For a fixed shell index, the positive indexed exponent makes the explicit
loss dominate the square-root saddle normalization.  The exact symmetric
Perron contribution on that shell therefore tends to zero in every critical
regime.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

/-- Exponential decay on `u^β / log u` absorbs `sqrt u` for every fixed
positive exponent `β`. -/
theorem tendsto_sqrt_mul_exp_neg_rpow_div_log_zero
    {u : ℕ → ℝ} (hu : Tendsto u atTop atTop) {β a : ℝ}
    (hβ : 0 < β) (ha : 0 < a) :
    Tendsto (fun n => Real.sqrt (u n) *
      Real.exp (-a * ((u n) ^ β / Real.log (u n))))
      atTop (𝓝 0) := by
  let γ := β / 2
  have hγ : 0 < γ := by dsimp only [γ]; linarith
  have hroot : Tendsto (fun n => (u n) ^ γ) atTop atTop :=
    (tendsto_rpow_atTop hγ).comp hu
  have hupper : Tendsto (fun n =>
      ((u n) ^ γ) ^ (1 / (2 * γ) : ℝ) *
        Real.exp (-a * (u n) ^ γ)) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (1 / (2 * γ)) a ha).comp hroot
  have hlogSmall := (isLittleO_log_rpow_atTop hγ).def
    (by norm_num : (0 : ℝ) < 1)
  refine squeeze_zero' (Eventually.of_forall fun n => mul_nonneg
    (Real.sqrt_nonneg _) (Real.exp_pos _).le) ?_ hupper
  filter_upwards [hu.eventually hlogSmall,
    hu.eventually (eventually_gt_atTop (1 : ℝ))] with n hlog huOne
  have huPos : 0 < u n := lt_trans zero_lt_one huOne
  have hlogPos : 0 < Real.log (u n) := Real.log_pos huOne
  have hrootPos : 0 < (u n) ^ γ := Real.rpow_pos_of_pos huPos _
  have hlogLe : Real.log (u n) ≤ (u n) ^ γ := by
    simpa only [Real.norm_eq_abs, abs_of_pos hlogPos,
      abs_of_pos hrootPos, one_mul] using hlog
  have hratio : (u n) ^ γ ≤ (u n) ^ β / Real.log (u n) := by
    rw [le_div_iff₀ hlogPos]
    calc
      (u n) ^ γ * Real.log (u n) ≤ (u n) ^ γ * (u n) ^ γ :=
        mul_le_mul_of_nonneg_left hlogLe hrootPos.le
      _ = (u n) ^ β := by
        rw [← Real.rpow_add huPos]
        congr 1
        dsimp only [γ]
        ring
  have hsqrt : ((u n) ^ γ) ^ (1 / (2 * γ) : ℝ) =
      Real.sqrt (u n) := by
    rw [← Real.rpow_mul huPos.le]
    have hprod : γ * (1 / (2 * γ) : ℝ) = 1 / 2 := by
      field_simp [hγ.ne']
    rw [hprod, ← Real.sqrt_eq_rpow]
  have hexp : Real.exp (-a * ((u n) ^ β / Real.log (u n))) ≤
      Real.exp (-a * (u n) ^ γ) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [hsqrt]
  exact mul_le_mul_of_nonneg_left hexp (Real.sqrt_nonneg _)

/-- For a fixed index, the exponential of the explicit indexed loss absorbs
the critical saddle normalization. -/
theorem IsTaoCriticalSmoothRegime.tendsto_sqrt_rankinRatio_mul_indexedOuterEnvelope_zero
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) (k : ℕ) :
    Tendsto (fun n =>
      Real.sqrt (smoothRankinRatio (X n) (y n)) *
        Real.exp (-(smoothSaddleIndexedOuterLossScale
          k (X n) (y n) / 96))) atTop (𝓝 0) := by
  let β := smoothSaddleIndexedOuterExponent k
  let C : ℝ := 15 * Real.log 4
  let a : ℝ := Real.exp (-16) /
    (C ^ β * (16 * Real.log 2) * 96)
  have hβ : 0 < β := by
    dsimp only [β]
    exact smoothSaddleIndexedOuterExponent_pos k
  have hC : 0 < C := by dsimp only [C]; positivity
  have ha : 0 < a := by dsimp only [a]; positivity
  have h := tendsto_sqrt_mul_exp_neg_rpow_div_log_zero
    (hregime.tendsto_rankinRatio_atTop hα) hβ ha
  apply h.congr'
  filter_upwards [(hregime.tendsto_rankinRatio_atTop hα).eventually
    (eventually_gt_atTop (1 : ℝ))] with n hu
  have huPos : 0 < smoothRankinRatio (X n) (y n) := lt_trans zero_lt_one hu
  have hlogu : Real.log (smoothRankinRatio (X n) (y n)) ≠ 0 :=
    (Real.log_pos hu).ne'
  congr 1
  apply congrArg Real.exp
  unfold smoothSaddleIndexedOuterLossScale
  dsimp only [a, C, β]
  rw [Real.div_rpow huPos.le hC.le]
  field_simp [hlogu, hC.ne',
    (Real.rpow_pos_of_pos hC (smoothSaddleIndexedOuterExponent k)).ne',
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  ring

/-- The indexed loss scale gives a uniform absolute envelope on both signs
of a fixed shell. -/
theorem IsTaoCriticalSmoothRegime.eventually_norm_smoothSaddlePerronLineIntegrand_le_indexedOuterEnvelope_abs
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      smoothSaddleIndexedOuterUpperHeight (k - 1) (y n) ≤ |t| →
      |t| ≤ smoothSaddleIndexedOuterUpperHeight k (y n) →
      ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleIndexedOuterLossScale
          k (X n) (y n) / 96)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_indexedOuterLossScale_le_cosineLoss hα hk] with
      n hX hy hsigma hloss
  intro t htLower htUpper
  have hlossT : smoothSaddleIndexedOuterLossScale k (X n) (y n) ≤
      smoothSaddleCosineLoss (y n) (smoothSaddlePoint (X n) (y n)) t := by
    by_cases ht : 0 ≤ t
    · have habs : |t| = t := abs_of_nonneg ht
      exact hloss t (by simpa [habs] using htLower)
        (by simpa [habs] using htUpper)
    · have habs : |t| = -t := abs_of_neg (lt_of_not_ge ht)
      have h := hloss (-t) (by simpa [habs] using htLower)
        (by simpa [habs] using htUpper)
      rw [smoothSaddleCosineLoss_neg] at h
      exact h
  calc
    ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleCosineLoss (y n)
          (smoothSaddlePoint (X n) (y n)) t / 96)) :=
      norm_smoothSaddlePerronLineIntegrand_le_cosineLoss
        hX hy hsigma.le t
    _ ≤ Real.exp (-(smoothSaddleIndexedOuterLossScale
        k (X n) (y n) / 96)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

noncomputable def smoothSaddleIndexedOuterPerronContribution
    (k X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleIndexedOuterUpperHeight (k - 1) y)
    (smoothSaddleIndexedOuterUpperHeight k y)

/-- Every fixed indexed symmetric outer-shell contribution tends to zero. -/
theorem IsTaoCriticalSmoothRegime.tendsto_indexedOuterPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ} (hregime : IsTaoCriticalSmoothRegime X y α)
    (hα : 0 < α) {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun n => smoothSaddleIndexedOuterPerronContribution
      k (X n) (y n)) atTop (𝓝 0) := by
  let C : ℝ :=
    (6 * (2 : ℝ) ^ (k - 2) * Real.pi * Real.sqrt 7) /
      Real.sqrt (2 * Real.pi)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hdecay :=
    hregime.tendsto_sqrt_rankinRatio_mul_indexedOuterEnvelope_zero hα k
  have hupper : Tendsto (fun n => C *
      (Real.sqrt (smoothRankinRatio (X n) (y n)) *
        Real.exp (-(smoothSaddleIndexedOuterLossScale
          k (X n) (y n) / 96)))) atTop (𝓝 0) := by
    simpa using hdecay.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_norm_smoothSaddlePerronLineIntegrand_le_indexedOuterEnvelope_abs
      hα hk] with n hX hy hsigma hpoint
  let E := Real.exp (-(smoothSaddleIndexedOuterLossScale
    k (X n) (y n) / 96))
  let L := smoothSaddleIndexedOuterUpperHeight (k - 1) (y n)
  let U := smoothSaddleIndexedOuterUpperHeight k (y n)
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hL : 0 ≤ L := by
    dsimp only [L, smoothSaddleIndexedOuterUpperHeight]
    positivity
  have hdouble : U = 2 * L := by
    dsimp only [U, L]
    rw [← show k - 1 + 1 = k by omega]
    exact smoothSaddleIndexedOuterUpperHeight_succ (by omega)
  have hLU : L ≤ U := by rw [hdouble]; linarith
  have hnorm := norm_smoothSaddleSymmetricPerronShellContribution_le
    hX hy hL hLU (E := E) hpoint
  have hwidth : U - L =
      (3 * (2 : ℝ) ^ (k - 2) * Real.pi) /
        Real.log (y n : ℝ) := by
    rw [hdouble]
    dsimp only [L, smoothSaddleIndexedOuterUpperHeight]
    have hsub : k - 1 - 1 = k - 2 := by omega
    rw [hsub]
    ring
  have hsd := smoothSaddleStandardDeviation_div_log_le_sqrt_rankinRatio
    hX hy hsigma.le
  have hsqrtMul : Real.sqrt (7 * smoothRankinRatio (X n) (y n)) =
      Real.sqrt 7 * Real.sqrt (smoothRankinRatio (X n) (y n)) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7)]
  change ‖smoothSaddleSymmetricPerronShellContribution
    (X n) (y n) L U‖ ≤ _
  rw [hwidth] at hnorm
  calc
    ‖smoothSaddleSymmetricPerronShellContribution (X n) (y n) L U‖ ≤
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.sqrt (2 * Real.pi)) *
          (2 * E * ((3 * (2 : ℝ) ^ (k - 2) * Real.pi) /
            Real.log (y n : ℝ))) := hnorm
    _ = (6 * (2 : ℝ) ^ (k - 2) * Real.pi /
          Real.sqrt (2 * Real.pi)) *
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.log (y n : ℝ) * E) := by
      field_simp [hlogy.ne', (Real.sqrt_pos.2 (by positivity :
        (0 : ℝ) < 2 * Real.pi)).ne']
      ring
    _ ≤ (6 * (2 : ℝ) ^ (k - 2) * Real.pi /
          Real.sqrt (2 * Real.pi)) *
        (Real.sqrt (7 * smoothRankinRatio (X n) (y n)) * E) := by
      gcongr
    _ = C * (Real.sqrt (smoothRankinRatio (X n) (y n)) * E) := by
      rw [hsqrtMul]
      dsimp only [C]
      ring

end

end Tao2026
