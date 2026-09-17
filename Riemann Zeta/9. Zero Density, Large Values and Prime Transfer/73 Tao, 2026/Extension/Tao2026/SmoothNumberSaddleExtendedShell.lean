import Tao2026.SmoothNumberSaddleFirstShellIntegral

/-!
# Extension of the first outer Perron shell

The accumulated CEP alphabet used on the first outer shell actually remains
in the nonpositive-cosine phase window up to physical height
`3*pi/(2*log y)`.  This module packages the newly covered adjacent segment
from `4*pi/(3*log y)` to that height, proves a reusable norm estimate for
symmetric Perron shells, and shows that the normalized adjacent contribution
tends to zero in every critical regime.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleSymmetricPerronShellContribution
    (X y : ℕ) (lower upper : ℝ) : ℂ :=
  ((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-upper)..(-lower),
        smoothSaddlePerronLineIntegrand X y t) +
      ∫ t in lower..upper, smoothSaddlePerronLineIntegrand X y t)

theorem norm_smoothSaddleSymmetricPerronShellContribution_le
    {X y : ℕ} (hX : 2 ≤ X) (hy : 2 ≤ y)
    {lower upper E : ℝ} (hlower : 0 ≤ lower) (hlu : lower ≤ upper)
    (hpoint : ∀ t : ℝ, lower ≤ |t| → |t| ≤ upper →
      ‖smoothSaddlePerronLineIntegrand X y t‖ ≤ E) :
    ‖smoothSaddleSymmetricPerronShellContribution X y lower upper‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * E * (upper - lower)) := by
  let f := smoothSaddlePerronLineIntegrand X y
  have hleft : ‖∫ t in (-upper)..(-lower), f t‖ ≤
      E * (upper - lower) := by
    calc
      ‖∫ t in (-upper)..(-lower), f t‖ ≤ E * |(-lower) - (-upper)| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le (by linarith : -upper ≤ -lower)] at ht
        apply hpoint t
        · rw [abs_of_nonpos (by linarith [ht.2, hlower] : t ≤ 0)]
          linarith [ht.2]
        · rw [abs_of_nonpos (by linarith [ht.2, hlower] : t ≤ 0)]
          linarith [ht.1]
      _ = E * (upper - lower) := by
        congr 1
        rw [show -lower - -upper = upper - lower by ring,
          abs_of_nonneg (sub_nonneg.mpr hlu)]
  have hright : ‖∫ t in lower..upper, f t‖ ≤
      E * (upper - lower) := by
    calc
      ‖∫ t in lower..upper, f t‖ ≤ E * |upper - lower| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le hlu] at ht
        apply hpoint t
        · rw [abs_of_nonneg (by linarith [ht.1, hlower] : 0 ≤ t)]
          exact ht.1.le
        · rw [abs_of_nonneg (by linarith [ht.1, hlower] : 0 ≤ t)]
          exact ht.2
      _ = E * (upper - lower) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hlu)]
  have hsd := smoothSaddleStandardDeviation_pos hX hy
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  unfold smoothSaddleSymmetricPerronShellContribution
  change ‖((smoothSaddleStandardDeviation X y : ℂ) /
      (Real.sqrt (2 * Real.pi) : ℂ)) *
    ((∫ t in (-upper)..(-lower), f t) + ∫ t in lower..upper, f t)‖ ≤
      (smoothSaddleStandardDeviation X y / Real.sqrt (2 * Real.pi)) *
        (2 * E * (upper - lower))
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
        (2 * E * (upper - lower)) := by
      gcongr
      linarith
    _ = _ := by rfl

noncomputable def smoothSaddleExtendedOuterUpperHeight (y : ℕ) : ℝ :=
  3 * Real.pi / (2 * Real.log (y : ℝ))

noncomputable def smoothSaddleExtendedOuterPerronContribution
    (X y : ℕ) : ℂ :=
  smoothSaddleSymmetricPerronShellContribution X y
    (smoothSaddleFirstOuterUpperHeight y)
    (smoothSaddleExtendedOuterUpperHeight y)

theorem IsTaoCriticalSmoothRegime.eventually_norm_smoothSaddlePerronLineIntegrand_le_extendedOuterEnvelope_abs
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      smoothSaddleFirstOuterUpperHeight (y n) ≤ |t| →
      |t| ≤ smoothSaddleExtendedOuterUpperHeight (y n) →
      ‖smoothSaddlePerronLineIntegrand (X n) (y n) t‖ ≤
        Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96)) := by
  filter_upwards [hregime.eventually_two_le_X,
    hregime.eventually_two_le_y hα,
    (hregime.tendsto_smoothSaddlePoint_one hα).eventually
      (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hregime.eventually_smoothSaddleFirstOuterLossScale_le_cosineLoss hα] with
      n hX hy hsigma hloss
  intro t htLower htUpper
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hbase : Real.pi / Real.log (y n : ℝ) ≤
      smoothSaddleFirstOuterUpperHeight (y n) := by
    rw [smoothSaddleFirstOuterUpperHeight]
    apply (div_le_div_iff₀ hlogy (mul_pos (by norm_num) hlogy)).mpr
    nlinarith [Real.pi_pos]
  have hlossT : smoothSaddleFirstOuterLossScale (X n) (y n) ≤
      smoothSaddleCosineLoss (y n) (smoothSaddlePoint (X n) (y n)) t := by
    by_cases ht : 0 ≤ t
    · have habs : |t| = t := abs_of_nonneg ht
      exact hloss t (by simpa [habs] using hbase.trans htLower)
        (by simpa [smoothSaddleExtendedOuterUpperHeight, habs] using htUpper)
    · have habs : |t| = -t := abs_of_neg (lt_of_not_ge ht)
      have h := hloss (-t) (by simpa [habs] using hbase.trans htLower)
        (by simpa [smoothSaddleExtendedOuterUpperHeight, habs] using htUpper)
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

theorem IsTaoCriticalSmoothRegime.tendsto_smoothSaddleExtendedOuterPerronContribution_zero
    {X y : ℕ → ℕ} {α : ℝ}
    (hregime : IsTaoCriticalSmoothRegime X y α) (hα : 0 < α) :
    Tendsto (fun n =>
      smoothSaddleExtendedOuterPerronContribution (X n) (y n))
      atTop (𝓝 0) := by
  let C : ℝ := Real.pi * Real.sqrt 7 / (3 * Real.sqrt (2 * Real.pi))
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
    hregime.eventually_norm_smoothSaddlePerronLineIntegrand_le_extendedOuterEnvelope_abs hα]
    with n hX hy hsigma hpoint
  let E := Real.exp (-(smoothSaddleFirstOuterLossScale (X n) (y n) / 96))
  let L := smoothSaddleFirstOuterUpperHeight (y n)
  let U := smoothSaddleExtendedOuterUpperHeight (y n)
  have hlogy : 0 < Real.log (y n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y n by omega))
  have hL : 0 ≤ L := by dsimp only [L, smoothSaddleFirstOuterUpperHeight]; positivity
  have hLU : L ≤ U := by
    dsimp only [L, U, smoothSaddleFirstOuterUpperHeight,
      smoothSaddleExtendedOuterUpperHeight]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hlogy)
      (mul_pos (by norm_num) hlogy)).mpr
    nlinarith [Real.pi_pos]
  have hnorm := norm_smoothSaddleSymmetricPerronShellContribution_le
    hX hy hL hLU (E := E) hpoint
  have hwidth : U - L = Real.pi / (6 * Real.log (y n : ℝ)) := by
    dsimp only [U, L, smoothSaddleExtendedOuterUpperHeight,
      smoothSaddleFirstOuterUpperHeight]
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
          (2 * E * (Real.pi / (6 * Real.log (y n : ℝ)))) := hnorm
    _ = (Real.pi / (3 * Real.sqrt (2 * Real.pi))) *
        (smoothSaddleStandardDeviation (X n) (y n) /
          Real.log (y n : ℝ) * E) := by
      field_simp [hlogy.ne', (Real.sqrt_pos.2 (by positivity :
        (0 : ℝ) < 2 * Real.pi)).ne']
      ring
    _ ≤ (Real.pi / (3 * Real.sqrt (2 * Real.pi))) *
        (Real.sqrt (7 * smoothRankinRatio (X n) (y n)) * E) := by
      gcongr
    _ = C * (Real.sqrt (smoothRankinRatio (X n) (y n)) * E) := by
      rw [hsqrtMul]
      dsimp only [C]
      ring

end

end Tao2026
