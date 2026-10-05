import DongWangWangZhang2026.DilationMeanSquare
import DongWangWangZhang2026.DilationSmoothing

/-!
# Damping-parameter assembly for the actual dilation

The original source line and maximizing twist stay fixed while the upper
logarithmic cutoff varies. Log-weight removal is split at the translation
scale to retain uniformity.
-/

namespace DongWangWangZhang2026

open MeasureTheory
noncomputable section

theorem measurable_logZetaSumDilation (t w : ℝ) : Measurable (logZetaSumDilation t w) :=
  (measurable_logZetaSum t).sub
    (measurable_const.mul ((measurable_logZetaSum t).comp (measurable_id.div_const w)))

theorem norm_normalized_logZetaDilation_exp_le (t : ℝ) {b u : ℝ}
    (hb : 0 ≤ b) (hu : 0 ≤ u) :
    Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ ≤ 2 * u := by
  have hfirst := norm_normalized_logZetaSum_exp_le t hu
  have hsecond : Real.exp (-u) *
      ‖(Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t‖ ≤ u := by
    by_cases hub : 0 ≤ u - b
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        ← mul_assoc, ← Real.exp_add, show -u + b = -(u - b) by ring]
      exact (norm_normalized_logZetaSum_exp_le t hub).trans (by linarith)
    · rw [logZetaSum_eq_zero_of_lt_one
        (Real.exp_lt_one_iff.mpr (lt_of_not_ge hub)), mul_zero, norm_zero, mul_zero]
      exact hu
  rw [logZetaSumDilation_exp]
  have htri := mul_le_mul_of_nonneg_left (norm_sub_le
    (logZetaSum (Real.exp u) t) ((Real.exp b : ℂ) * logZetaSum (Real.exp (u - b)) t))
      (Real.exp_pos (-u)).le
  linarith

theorem normalized_zetaDilation_exp_le_logDilation (t : ℝ) {b u : ℝ}
    (hb : 0 ≤ b) (hu : 0 < u) :
    Real.exp (-u) * ‖zetaSumDilation t (Real.exp b) (Real.exp u)‖ ≤
      Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u + (2 + b) / u := by
  have h := (norm_sub_norm_le ((Real.log (Real.exp u) : ℂ) *
    zetaSumDilation t (Real.exp b) (Real.exp u))
      (logZetaSumDilation t (Real.exp b) (Real.exp u))).trans
        (norm_log_mul_zetaSumDilation_sub_logDilation_le t (Real.one_le_exp hb) (Real.exp_pos u))
  rw [Real.log_exp, Real.log_exp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le] at h
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-u)).le
  have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  rw [← mul_assoc, he, one_mul] at hmul
  rw [← add_div]
  apply (le_div_iff₀ hu).mpr
  nlinarith

theorem intervalIntegrable_normalized_logDilation_div (t : ℝ) {b a Y : ℝ}
    (hb : 0 ≤ b) (ha : 0 < a) (haY : a ≤ Y) :
    IntervalIntegrable (fun u : ℝ => Real.exp (-u) *
      ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u) volume a Y := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le haY]
  apply Measure.integrableOn_of_bounded (by simp)
    ((((Real.measurable_exp.comp measurable_neg).mul
      ((measurable_logZetaSumDilation t (Real.exp b)).comp Real.measurable_exp).norm).div
        measurable_id).aestronglyMeasurable) (M := 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := ha.trans hu.1
  change ‖Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u‖ ≤ 2
  rw [Real.norm_of_nonneg (by positivity)]
  exact (div_le_iff₀ hu0).mpr (norm_normalized_logZetaDilation_exp_le t hb hu0.le)

/-- Split at the translation scale, retaining the ratio inside the logarithm. -/
theorem integral_normalized_zetaDilation_le_logDilation (t : ℝ) {b Y : ℝ}
    (hb : 0 ≤ b) (hY : b + 1 ≤ Y) :
    (∫ u : ℝ in 0..Y, Real.exp (-u) * ‖zetaSumDilation t (Real.exp b) (Real.exp u)‖) ≤
      2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
        ∫ u : ℝ in 1..Y, Real.exp (-u) *
          ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u := by
  have ha : 0 < b + 1 := by linarith
  have hY0 : 0 < Y := ha.trans_le hY
  have hsmall : (∫ u : ℝ in 0..b + 1,
      Real.exp (-u) * ‖zetaSumDilation t (Real.exp b) (Real.exp u)‖) ≤ 2 * (b + 1) := by
    calc
      _ ≤ ∫ _u : ℝ in 0..b + 1, (2 : ℝ) := intervalIntegral.integral_mono_on ha.le
        (intervalIntegrable_normalized_zetaSumDilation_exp t 0 (b + 1) (Real.exp_pos b))
        intervalIntegrable_const (fun u _ => by
          calc
            _ ≤ Real.exp (-u) * (2 * Real.exp u) := mul_le_mul_of_nonneg_left
              (norm_zetaSumDilation_le t (Real.exp_pos b) (Real.exp_pos u).le) (Real.exp_pos _).le
            _ = 2 := by rw [← mul_assoc, mul_comm _ (2 : ℝ), mul_assoc, ← Real.exp_add]; simp)
      _ = _ := by simp; ring
  have hinv : IntervalIntegrable (fun u : ℝ => (2 + b) / u) volume (b + 1) Y := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hY] at hu
    have hu0 := ha.trans_le hu.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hlogInt := intervalIntegrable_normalized_logDilation_div t hb ha hY
  have hlarge := intervalIntegral.integral_mono_on hY
    (intervalIntegrable_normalized_zetaSumDilation_exp t (b + 1) Y (Real.exp_pos b))
    (hlogInt.add hinv)
    (fun u hu => normalized_zetaDilation_exp_le_logDilation t hb (ha.trans_le hu.1))
  rw [intervalIntegral.integral_add hlogInt hinv] at hlarge
  have hinvEq : (∫ u : ℝ in b + 1..Y, (2 + b) / u) =
      (2 + b) * Real.log (Y / (b + 1)) := by
    simp_rw [div_eq_mul_one_div (2 + b)]
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha hY0]
  rw [hinvEq] at hlarge
  have henlarge := intervalIntegral.integral_mono_interval (show (1 : ℝ) ≤ b + 1 by linarith)
    hY le_rfl (Filter.Eventually.of_forall (fun u => show
      0 ≤ Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u from by
        by_cases hu : 0 ≤ u
        · positivity
        · rw [logZetaSumDilation_exp, logZetaSum_eq_zero_of_lt_one
            (Real.exp_lt_one_iff.mpr (lt_of_not_ge hu)),
            logZetaSum_eq_zero_of_lt_one (Real.exp_lt_one_iff.mpr (by linarith))]
          simp))
    (intervalIntegrable_normalized_logDilation_div t hb zero_lt_one (by linarith : 1 ≤ Y))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_normalized_zetaSumDilation_exp t 0 (b + 1) (Real.exp_pos b))
    (intervalIntegrable_normalized_zetaSumDilation_exp t (b + 1) Y (Real.exp_pos b))]
  linarith

theorem integral_damped_logDilation_le_sqrt (t b : ℝ) {δ Y : ℝ} (hδ : 0 < δ) (hY : 1 ≤ Y) :
    (∫ u : ℝ in 1..Y, Real.exp (-(1 + 2 * δ) * u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖) ≤
      Real.sqrt (1 / (2 * δ)) * Real.sqrt
        (∫ u : ℝ, Real.exp (-2 * (1 + δ) * u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 1 Y)
  let f : ℝ → ℝ := fun u => Real.exp (-δ * u)
  let g : ℝ → ℝ := fun u => ‖dampedLogZetaDifference t (1 + δ) b u‖
  have hf : MemLp f 2 μ := by
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change ‖Real.exp (-δ * u)‖ ≤ 1
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (by linarith [hu.1])
  have hg : MemLp g 2 μ := (memLp_dampedLogZetaDifference_two t b (by linarith : 1 < 1 + δ)).norm.restrict _
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := μ) (f := f) (g := g)
    (Filter.Eventually.of_forall (fun u => (Real.exp_pos (-δ * u)).le))
    (Filter.Eventually.of_forall (fun u => norm_nonneg (dampedLogZetaDifference t (1 + δ) b u)))
    (by simpa using hf) (by simpa using hg)
  have hfbound : (∫ u, f u ^ 2 ∂μ) ≤ 1 / (2 * δ) := by
    have he (u : ℝ) : f u ^ 2 = Real.exp ((-2 * δ) * u) := by
      dsimp [f]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simp_rw [he]
    calc
      _ ≤ ∫ u : ℝ in Set.Ioi 0, Real.exp ((-2 * δ) * u) :=
        setIntegral_mono_set (integrableOn_exp_mul_Ioi (by linarith : -2 * δ < 0) 0)
          (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
          (Filter.Eventually.of_forall fun _u hu => lt_trans zero_lt_one hu.1)
      _ = _ := by rw [integral_exp_mul_Ioi (by linarith : -2 * δ < 0) 0]; simp
  have hgnorm (u : ℝ) : g u ^ 2 =
      Real.exp (-2 * (1 + δ) * u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ ^ 2 := by
    dsimp only [g]
    rw [dampedLogZetaDifference_eq_actual, ← logZetaSumDilation_exp]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
      ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hgbound : (∫ u, g u ^ 2 ∂μ) ≤
      ∫ u : ℝ, Real.exp (-2 * (1 + δ) * u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ ^ 2 := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hgnorm)]
    exact setIntegral_le_integral
      ((memLp_two_iff_integrable_sq ((memLp_dampedLogZetaDifference_two t b
        (by linarith : 1 < 1 + δ)).norm.aestronglyMeasurable)).mp
          (memLp_dampedLogZetaDifference_two t b (by linarith : 1 < 1 + δ)).norm)
      (Filter.Eventually.of_forall (fun u => sq_nonneg (g u)))
  have hfg (u : ℝ) : f u * g u =
      Real.exp (-(1 + 2 * δ) * u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ := by
    dsimp only [f, g]
    rw [dampedLogZetaDifference_eq_actual, ← logZetaSumDilation_exp]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hc' : (∫ u, f u * g u ∂μ) ≤
      Real.sqrt (∫ u, f u ^ 2 ∂μ) * Real.sqrt (∫ u, g u ^ 2 ∂μ) := by
    simpa only [Real.sqrt_eq_rpow, one_div, Real.rpow_two] using hc
  rw [intervalIntegral.integral_of_le hY]
  simp_rw [hfg] at hc'
  exact hc'.trans (mul_le_mul (Real.sqrt_le_sqrt hfbound) (Real.sqrt_le_sqrt hgbound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Reconstruction up to twice the base logarithmic cutoff, without moving
the source line leftward or reselecting its maximizing twist. -/
theorem reciprocal_le_damping_parameter_double {L u : ℝ}
    (hL : 0 < L) (hu : 1 ≤ u) (huL : u ≤ 2 * L) :
    1 / u ≤ 324 * ∫ α : ℝ in 0..(1 / 2 : ℝ), Real.exp (-2 * (1 / L + α) * u) := by
  have hu0 : 0 < u := by linarith
  rw [integral_damping_parameter L hu0]
  have hsmall : (1 / 81 : ℝ) ≤ Real.exp (-2 * u / L) := by
    have he2 : Real.exp (2 : ℝ) ≤ 9 := by
      have he1 := Real.exp_one_lt_three
      have he1pos := Real.exp_pos (1 : ℝ)
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have he4 : Real.exp (4 : ℝ) ≤ 81 := by
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
      nlinarith [Real.exp_pos (2 : ℝ)]
    have hneg : (1 / 81 : ℝ) ≤ Real.exp (-4 : ℝ) := by
      rw [Real.exp_neg, ← one_div]
      exact (le_div_iff₀ (Real.exp_pos 4)).mpr (by nlinarith)
    apply hneg.trans (Real.exp_le_exp.mpr ?_)
    exact (le_div_iff₀ hL).mpr (by linarith)
  have hlarge : (1 / 2 : ℝ) ≤ 1 - Real.exp (-u) := by
    have he1 := Real.exp_one_gt_two
    have he : Real.exp (-u) ≤ (1 / 2 : ℝ) := by
      apply (Real.exp_le_exp.mpr (neg_le_neg hu)).trans
      rw [Real.exp_neg, ← one_div]
      exact (div_le_div_iff₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
    linarith
  have hp := mul_le_mul hsmall hlarge (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.exp_pos _).le
  calc
    _ ≤ (162 * (Real.exp (-2 * u / L) * (1 - Real.exp (-u)))) / u :=
      div_le_div_of_nonneg_right (by nlinarith) hu0.le
    _ = _ := by ring

theorem integrable_dilation_damping_rectangle (t : ℝ) {b L Y : ℝ}
    (hb : 0 ≤ b) (hL : 0 < L) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(1 + 2 * (1 / L + p.2)) * p.1) * ‖logZetaSumDilation t (Real.exp b) (Real.exp p.1)‖)
      ((volume.restrict (Set.Ioc 1 Y)).prod (volume.restrict (Set.Ioc 0 (1 / 2 : ℝ)))) := by
  rw [Measure.prod_restrict]
  apply Measure.integrableOn_of_bounded (by simp; finiteness)
    (((by fun_prop : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(1 + 2 * (1 / L + p.2)) * p.1))).mul
        (((measurable_logZetaSumDilation t (Real.exp b)).comp
          (Real.measurable_exp.comp measurable_fst)).norm)).aestronglyMeasurable) (M := 2 * Y)
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  change ‖Real.exp (-(1 + 2 * (1 / L + p.2)) * p.1) *
    ‖logZetaSumDilation t (Real.exp b) (Real.exp p.1)‖‖ ≤ 2 * Y
  rw [Real.norm_of_nonneg (by positivity)]
  have hL0 : 0 < L := hL
  have hp0 : 0 ≤ p.1 := by linarith [hp.1.1]
  have hδ : 0 ≤ 1 / L + p.2 := add_nonneg (one_div_nonneg.mpr hL0.le) hp.2.1.le
  have he : -(1 + 2 * (1 / L + p.2)) * p.1 =
      -2 * (1 / L + p.2) * p.1 + -p.1 := by ring
  rw [he, Real.exp_add, mul_assoc]
  calc
    _ ≤ 1 * (2 * p.1) := mul_le_mul
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hp0))
      (norm_normalized_logZetaDilation_exp_le t hb hp0) (by positivity) (by norm_num)
    _ ≤ 2 * Y := by linarith [hp.1.2]

/-- A finite, absolutely integrable parameter exchange for the actual weighted
sum. This is the reciprocal-weight reconstruction used in mean-value assembly. -/
theorem integral_normalized_logDilation_le_damping_average (t : ℝ) {b L Y : ℝ}
    (hb : 0 ≤ b) (hL : 0 < L) (hY : 1 ≤ Y) (hYL : Y ≤ 2 * L) :
    (∫ u : ℝ in 1..Y, Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ / u) ≤
      324 * ∫ α : ℝ in 0..(1 / 2 : ℝ),
        ∫ u : ℝ in 1..Y, Real.exp (-(1 + 2 * (1 / L + α)) * u) *
          ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ := by
  let F : ℝ → ℝ → ℝ := fun u α =>
    Real.exp (-(1 + 2 * (1 / L + α)) * u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖
  have hF := integrable_dilation_damping_rectangle (Y := Y) t hb hL
  have hinner : IntervalIntegrable (fun u => ∫ α : ℝ in 0..(1 / 2 : ℝ), F u α) volume 1 Y := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hY]
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      using hF.integral_prod_left
  have hbound := intervalIntegral.integral_mono_on hY
    (intervalIntegrable_normalized_logDilation_div t hb zero_lt_one hY) (hinner.const_mul 324) (fun u hu => by
      have hrec := mul_le_mul_of_nonneg_left (reciprocal_le_damping_parameter_double hL hu.1 (hu.2.trans hYL))
        (show 0 ≤ Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖ by positivity)
      have hfactor : (∫ α : ℝ in 0..(1 / 2 : ℝ), F u α) =
          (Real.exp (-u) * ‖logZetaSumDilation t (Real.exp b) (Real.exp u)‖) *
            ∫ α : ℝ in 0..(1 / 2 : ℝ), Real.exp (-2 * (1 / L + α) * u) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro α _
        dsimp [F]
        rw [mul_right_comm, ← Real.exp_add]
        congr 2
        ring
      rw [hfactor]
      convert hrec using 1 <;> ring)
  rw [intervalIntegral.integral_const_mul] at hbound
  have hswap : (∫ u : ℝ in 1..Y, ∫ α : ℝ in 0..(1 / 2 : ℝ), F u α) =
      ∫ α : ℝ in 0..(1 / 2 : ℝ), ∫ u : ℝ in 1..Y, F u α := by
    simp_rw [intervalIntegral.integral_of_le hY,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact integral_integral_swap hF
  rwa [hswap] at hbound

/-- The proved capped spectral majorant after weighted Cauchy–Schwarz. -/
def dilationDampingBound (L R α : ℝ) : ℝ :=
  Real.sqrt (1 / (2 * (1 / L + α))) * Real.sqrt
    ((min R (4 / (1 / L + α))) ^ 2 * (Real.log 4 + 4) ^ 2 / (2 * (1 / L + α)) +
      4 * ((2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
        (4 / L + 16 / ((1 / L + α) ^ 3 * L ^ 2)))))

theorem continuousOn_dilationDampingBound {L : ℝ} (hL : 0 < L) (R : ℝ) :
    ContinuousOn (dilationDampingBound L R) (Set.Icc 0 (1 / 2 : ℝ)) := by
  intro α hα
  have hδ : 0 < 1 / L + α := add_pos_of_pos_of_nonneg (one_div_pos.mpr hL) hα.1
  apply ContinuousAt.continuousWithinAt
  unfold dilationDampingBound
  fun_prop (disch := positivity)

/-- The same original maximizer controls the complete parameter expression
for every upper cutoff up to twice its logarithmic scale. -/
theorem exists_maximizingTwist_dilation_parameter_bound (A : ℕ) (hA : 1 ≤ A) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b Y : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → b + 1 ≤ Y → Y ≤ 2 * Real.log x →
      Real.exp (-Y) * ‖zetaSum (Real.exp Y) (t - t₀) -
        (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) (t - t₀)‖ ≤
          2048 / Y * (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
            324 * ∫ α : ℝ in 0..(1 / 2 : ℝ), dilationDampingBound (Real.log x)
              (4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
                (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) + 16) α) +
            (1904642 + b) / Y := by
  obtain ⟨B, hB, hmean⟩ := exists_maximizingTwist_weighted_dilation_mean_square_min A hA
  refine ⟨B, hB, ?_⟩
  intro x t t₀ b Y hx hlog16 hscale hmax ht₀ hb hbY hYL
  let L := Real.log x
  let R := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ ((A : ℝ)⁻¹))) / L) ^ (38 / 113 : ℝ) + 16
  have hL : 0 < L := Real.log_pos hx
  have hY : 1 ≤ Y := by linarith
  have hmoment (α : ℝ) (hα : 0 < α) (hαtop : α ≤ 1 / 2) :
      (∫ u : ℝ in 1..Y, Real.exp (-(1 + 2 * (1 / L + α)) * u) *
        ‖logZetaSumDilation (t - t₀) (Real.exp b) (Real.exp u)‖) ≤
          dilationDampingBound L R α := by
    have hδ : 0 < 1 / L + α := add_pos (one_div_pos.mpr hL) hα
    have hδtop : 1 / L + α ≤ 1 := by
      have hi : 1 / L ≤ (1 / 16 : ℝ) :=
        (div_le_div_iff₀ hL (by norm_num)).mpr (by simpa only [L, one_mul] using hlog16)
      linarith
    have hms := hmean x t t₀ b α hx hlog16 hscale hmax ht₀ hb hα hδtop
    have hc := integral_damped_logDilation_le_sqrt (t - t₀) b hδ hY
    simp only [logZetaSumDilation_exp, ← add_assoc] at hc
    simpa only [logZetaSumDilation_exp, dilationDampingBound, L, R] using
      hc.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hms) (Real.sqrt_nonneg _))
  have hF := (integrable_dilation_damping_rectangle (Y := Y) (t - t₀) hb hL).integral_prod_right
  have hi : IntervalIntegrable (fun α : ℝ => ∫ u : ℝ in 1..Y,
      Real.exp (-(1 + 2 * (1 / L + α)) * u) *
        ‖logZetaSumDilation (t - t₀) (Real.exp b) (Real.exp u)‖) volume 0 (1 / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simpa only [intervalIntegral.integral_of_le hY] using hF
  have hparam := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hi ((continuousOn_dilationDampingBound hL R).intervalIntegrable_of_Icc (by norm_num))
    (by
      rw [← restrict_Ioc_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact hmoment α hα.1 hα.2)
  have hweight := integral_normalized_logDilation_le_damping_average (t - t₀) hb hL hY hYL
  have havg := integral_normalized_zetaDilation_le_logDilation (t - t₀) hb hbY
  have hwhole : (∫ u : ℝ in 0..Y,
      Real.exp (-u) * ‖zetaSumDilation (t - t₀) (Real.exp b) (Real.exp u)‖) ≤
      2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
        324 * ∫ α : ℝ in 0..(1 / 2 : ℝ), dilationDampingBound L R α := by
    linarith
  simp only [zetaSumDilation_exp] at hwhole
  exact (norm_exp_dilation_le_log_average (t - t₀) hb (by linarith : 0 < Y)).trans
    (add_le_add (mul_le_mul_of_nonneg_left hwhole (by positivity : 0 ≤ 2048 / Y)) le_rfl)

/-- Reuse the already evaluated ordinary parameter majorant. The dilation
costs at most a factor four, with its reciprocal cap still retained. -/
theorem dilationDampingBound_le_four_meanValueDampingBound {L R α : ℝ}
    (hL : 0 < L) (hR : 0 ≤ R) (hα : 0 ≤ α) :
    dilationDampingBound L R α ≤ 4 * meanValueDampingBound L R α := by
  let δ := 1 / L + α
  let K := (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4))
  let C := Real.log 4 + 4
  let M := min (R + (1 + L) * (4 * α / (Real.pi * L))) (1 + 1 / δ)
  have hδ : 0 < δ := add_pos_of_pos_of_nonneg (one_div_pos.mpr hL) hα
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmin : min R (4 / δ) ≤ 4 * M := by
    dsimp only [M]
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4)]
    apply min_le_min
    · have he : 0 ≤ (1 + L) * (4 * α / (Real.pi * L)) := by positivity
      nlinarith only [he, hR]
    · rw [div_eq_mul_one_div 4]
      linarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ min R (4 / δ)) hmin 2
  have hmain := mul_le_mul_of_nonneg_right hsq (show 0 ≤ C ^ 2 / (2 * δ) by positivity)
  have htail : 4 * K * (4 / L + 16 / (δ ^ 3 * L ^ 2)) ≤
      16 * (K * (2 / L + 4 / (δ ^ 3 * L ^ 2))) := by
    have hpos : 0 ≤ K / L := div_nonneg hK hL.le
    simp only [div_eq_mul_inv] at hpos ⊢
    nlinarith only [hpos]
  have hQ : (min R (4 / δ)) ^ 2 * C ^ 2 / (2 * δ) +
      4 * (K * (4 / L + 16 / (δ ^ 3 * L ^ 2))) ≤
      16 * (M ^ 2 * C ^ 2 / (2 * δ) + K * (2 / L + 4 / (δ ^ 3 * L ^ 2))) := by
    simp only [div_eq_mul_inv] at hmain htail ⊢
    nlinarith only [hmain, htail]
  have hsqrt := Real.sqrt_le_sqrt hQ
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), show Real.sqrt (16 : ℝ) = 4 by norm_num] at hsqrt
  have hmul := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (1 / (2 * δ)))
  have hfinal := hmul.trans_eq (mul_left_comm _ (4 : ℝ) _)
  simpa only [dilationDampingBound, meanValueDampingBound, δ, K, C, M, mul_assoc] using hfinal

theorem integral_dilationDampingBound_le {L R : ℝ} (hL : 8 ≤ L)
    (hR : 0 ≤ R) (hRtop : R ≤ 1 + L) :
    (∫ α : ℝ in 0..(1 / 2 : ℝ), dilationDampingBound L R α) ≤
      4 * meanValueAssemblyConstant *
        ((R + 4) * (1 + Real.log (2 * L / (R + 4))) + 2) := by
  have hL0 : 0 < L := by linarith
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ((continuousOn_dilationDampingBound hL0 R).intervalIntegrable_of_Icc (by norm_num))
    (((continuousOn_meanValueDampingBound hL0 R).intervalIntegrable_of_Icc
      (by norm_num)).const_mul 4)
    (fun α hα => dilationDampingBound_le_four_meanValueDampingBound hL0 hR hα.1)
  rw [intervalIntegral.integral_const_mul] at hm
  exact hm.trans (by
    convert mul_le_mul_of_nonneg_left (integral_meanValueDampingBound_le hL hR hRtop)
      (by norm_num : (0 : ℝ) ≤ 4) using 1
    ring)

theorem min_le_geometric_rpow {a b q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hq : 0 ≤ q) (hq₁ : q ≤ 1) : min a b ≤ a ^ q * b ^ (1 - q) := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    calc
      a = a ^ q * a ^ (1 - q) := by rw [← Real.rpow_add ha]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ha.le hab (by linarith)) (Real.rpow_nonneg ha.le q)
  · rw [min_eq_right hba]
    calc
      b = b ^ q * b ^ (1 - q) := by rw [← Real.rpow_add hb]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hb.le hba hq) (Real.rpow_nonneg hb.le (1 - q))

/-- A small power loss integrates the reciprocal cap on its entire range;
no upper-size premise on the maximum is required. -/
theorem integral_min_reciprocal_le_rpow {a b R q : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hR : 0 < R) (hq : 0 < q) (hq₁ : q < 1) :
    (∫ u : ℝ in a..b, min R (2 / u) / u) ≤
      R ^ q * (2 : ℝ) ^ (1 - q) * a ^ (q - 1) / (1 - q) := by
  have hf : IntervalIntegrable (fun u : ℝ => min R (2 / u) / u) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    have hu0 := ha.trans_le hu.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hg : IntervalIntegrable (fun u : ℝ => u ^ (q - 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    have hu0 := ha.trans_le hu.1
    exact (Real.continuousAt_rpow_const u (q - 2) (Or.inl hu0.ne')).continuousWithinAt
  have hm := intervalIntegral.integral_mono_on hab hf
    (hg.const_mul (R ^ q * (2 : ℝ) ^ (1 - q))) (fun u hu => by
      have hu0 := ha.trans_le hu.1
      have hmin := div_le_div_of_nonneg_right
        (min_le_geometric_rpow hR (by positivity : 0 < 2 / u) hq.le hq₁.le) hu0.le
      have he : (R ^ q * (2 / u) ^ (1 - q)) / u =
          (R ^ q * (2 : ℝ) ^ (1 - q)) * u ^ (q - 2) := by
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hu0.le,
          show q - 2 = -(1 - q) - 1 by ring, Real.rpow_sub hu0 (-(1 - q)) 1,
          Real.rpow_one, Real.rpow_neg hu0.le (1 - q)]
        ring
      exact hmin.trans_eq he)
  rw [intervalIntegral.integral_const_mul] at hm
  have ht : (∫ u : ℝ in a..b, u ^ (q - 2)) ≤
      a ^ (q - 1) / (1 - q) := by
    rw [intervalIntegral.integral_of_le hab]
    calc
      _ ≤ ∫ u : ℝ in Set.Ioi a, u ^ (q - 2) :=
        setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt (by linarith : q - 2 < -1) ha)
          (by
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
            exact Real.rpow_nonneg (ha.le.trans hu.le) _)
          (Filter.Eventually.of_forall (fun _u hu => hu.1))
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by linarith : q - 2 < -1) ha,
          show q - 2 + 1 = q - 1 by ring]
        rw [show 1 - q = -(q - 1) by ring]
        simp only [div_neg, neg_div]
  exact hm.trans (by
    convert mul_le_mul_of_nonneg_left ht
      (show 0 ≤ R ^ q * (2 : ℝ) ^ (1 - q) by positivity) using 1
    ring)

/-- Power-loss evaluation is uniform in the size of the zeta maximum. -/
theorem integral_dilationDampingBound_le_rpow {L R q : ℝ} (hL : 8 ≤ L)
    (hR : 0 ≤ R) (hq : 0 < q) (hq₁ : q < 1) :
    (∫ α : ℝ in 0..(1 / 2 : ℝ), dilationDampingBound L R α) ≤
      4 * meanValueAssemblyConstant *
        ((R + 4) ^ q * (2 : ℝ) ^ (1 - q) * L ^ (1 - q) / (1 - q) + 2) := by
  let a := 1 / L
  let Q := R + 4
  have hL0 : 0 < L := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ : 0 < Q := by dsimp [Q]; linarith
  let F : ℝ → ℝ := fun α => min Q (2 / (a + α)) / (a + α)
  let G : ℝ → ℝ := fun α => 1 / ((a + α) ^ 2 * L)
  have hF : IntervalIntegrable F volume 0 (1 / 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro α hα
    have hδ : 0 < a + α := add_pos_of_pos_of_nonneg ha hα.1
    apply ContinuousAt.continuousWithinAt
    dsimp [F]
    fun_prop (disch := positivity)
  have hG : IntervalIntegrable G volume 0 (1 / 2) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro α hα
    have hδ : 0 < a + α := add_pos_of_pos_of_nonneg ha hα.1
    apply ContinuousAt.continuousWithinAt
    dsimp [G]
    fun_prop (disch := positivity)
  have hFeq : (∫ α : ℝ in 0..(1 / 2 : ℝ), F α) =
      ∫ u : ℝ in a..a + 1 / 2, min Q (2 / u) / u := by
    simpa only [F, add_zero] using intervalIntegral.integral_comp_add_left
      (a := 0) (b := 1 / 2) (fun u : ℝ => min Q (2 / u) / u) a
  have hFbound : (∫ α : ℝ in 0..(1 / 2 : ℝ), F α) ≤
      Q ^ q * (2 : ℝ) ^ (1 - q) * L ^ (1 - q) / (1 - q) := by
    rw [hFeq]
    have he : a ^ (q - 1) = L ^ (1 - q) := by
      dsimp only [a]
      rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
      congr 1
      ring
    simpa only [he] using integral_min_reciprocal_le_rpow ha
      (by linarith : a ≤ a + 1 / 2) hQ hq hq₁
  have hGeq : (∫ α : ℝ in 0..(1 / 2 : ℝ), G α) =
      1 / L * (1 / a - 1 / (a + 1 / 2)) := by
    have he (α : ℝ) : G α = 1 / L * (1 / (a + α) ^ 2) := by
      simp only [G, one_div, mul_inv_rev]
    simp_rw [he]
    rw [intervalIntegral.integral_const_mul]
    have hshift := intervalIntegral.integral_comp_add_left
      (a := 0) (b := 1 / 2) (fun u : ℝ => 1 / u ^ 2) a
    simp only [add_zero] at hshift
    rw [hshift, integral_reciprocal_sq 1 ha (by linarith : a ≤ a + 1 / 2)]
  have hGbound : (∫ α : ℝ in 0..(1 / 2 : ℝ), G α) ≤ 1 := by
    rw [hGeq]
    have he : 1 / L * (1 / a) = 1 := by dsimp [a]; field_simp
    have hpos : 0 ≤ 1 / L * (1 / (a + 1 / 2)) := by positivity
    nlinarith
  have hbound := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ((continuousOn_dilationDampingBound hL0 R).intervalIntegrable_of_Icc (by norm_num))
    (((hF.add (intervalIntegrable_const (c := (1 : ℝ)))).add hG).const_mul
      (4 * meanValueAssemblyConstant))
    (fun α hα => (dilationDampingBound_le_four_meanValueDampingBound hL0 hR hα.1).trans (by
      convert mul_le_mul_of_nonneg_left
        (meanValueDampingBound_le (by linarith : 2 ≤ L) hR hα.1 hα.2)
          (by norm_num : (0 : ℝ) ≤ 4) using 1
      dsimp [F, G, Q, a]
      ring))
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hF.add intervalIntegrable_const) hG,
    intervalIntegral.integral_add hF intervalIntegrable_const] at hbound
  norm_num only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) meanValueAssemblyConstant_pos.le))

/-- Evaluated actual-difference bound with every analytic input discharged.
The power-loss parameter can be chosen close to one for the final exponent. -/
theorem exists_maximizingTwist_dilation_power_bound (A : ℕ) (hA : 1 ≤ A)
    {q : ℝ} (hq : 0 < q) (hq₁ : q < 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x t t₀ b Y : ℝ, 1 < x → 16 ≤ Real.log x → B ≤ Real.log x →
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) →
      |t₀| ≤ Real.log x / 2 → 0 ≤ b → b + 1 ≤ Y → Y ≤ 2 * Real.log x →
      let R := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + Real.log x) *
        (max B (max b ((Real.log x) ^ ((A : ℝ)⁻¹))) / Real.log x) ^ (38 / 113 : ℝ) + 16
      Real.exp (-Y) * ‖zetaSum (Real.exp Y) (t - t₀) -
        (Real.exp b : ℂ) * zetaSum (Real.exp (Y - b)) (t - t₀)‖ ≤
          2048 / Y * (2 * (b + 1) + (2 + b) * Real.log (Y / (b + 1)) +
            1296 * meanValueAssemblyConstant *
              ((R + 4) ^ q * (2 : ℝ) ^ (1 - q) *
                (Real.log x) ^ (1 - q) / (1 - q) + 2)) + (1904642 + b) / Y := by
  obtain ⟨B, hB, hsource⟩ := exists_maximizingTwist_dilation_parameter_bound A hA
  refine ⟨B, hB, ?_⟩
  intro x t t₀ b Y hx hlog16 hscale hmax ht₀ hb hbY hYL
  let L := Real.log x
  let R := 4 * Real.exp (4 * (Real.log 4 + 4) + 12) * (1 + L) *
    (max B (max b (L ^ ((A : ℝ)⁻¹))) / L) ^ (38 / 113 : ℝ) + 16
  have hL : 0 < L := Real.log_pos hx
  have hR : 0 ≤ R := by
    have hmaxB : 0 ≤ max B (max b (L ^ ((A : ℝ)⁻¹))) := le_trans (by linarith : 0 ≤ B)
      (le_max_left _ _)
    dsimp only [R]
    positivity
  have heval := integral_dilationDampingBound_le_rpow (L := L) (R := R)
    (by dsimp only [L]; linarith : 8 ≤ L) hR hq hq₁
  have hY : 0 < Y := by linarith
  have h := hsource x t t₀ b Y hx hlog16 hscale hmax ht₀ hb hbY hYL
  apply h.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2048 / Y)
  have hm := mul_le_mul_of_nonneg_left heval (by norm_num : (0 : ℝ) ≤ 324)
  dsimp only [L, R] at hm
  linarith only [hm]

end
end DongWangWangZhang2026
