import DongWangWangZhang2026.MeanValueSmoothing
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Damping-parameter assembly for the actual phase sum

This module connects the pointwise smoothing inequality to the weighted
mean-square estimate. The sums retain their real cutoffs and spectral height.
-/

open MeasureTheory Complex
open scoped BigOperators

namespace DongWangWangZhang2026
noncomputable section

theorem norm_normalized_zetaSum_exp_le (t u : ℝ) :
    Real.exp (-u) * ‖zetaSum (Real.exp u) t‖ ≤ 1 := by
  calc
    _ ≤ Real.exp (-u) * Real.exp u := mul_le_mul_of_nonneg_left
      (norm_zetaSum_le (Real.exp_pos _).le t) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem norm_normalized_logZetaSum_exp_le (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ ≤ u := by
  have h := norm_logZetaSum_le (Real.one_le_exp_iff.mpr hu) t
  rw [Real.log_exp] at h
  calc
    _ ≤ Real.exp (-u) * (Real.exp u * u) :=
      mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = u := by rw [← mul_assoc, ← Real.exp_add]; simp

/-- Removing the logarithmic weight costs the explicit reciprocal variable. -/
theorem normalized_zetaSum_exp_le_logSum (t : ℝ) {u : ℝ} (hu : 0 < u) :
    Real.exp (-u) * ‖zetaSum (Real.exp u) t‖ ≤
      Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ / u + 1 / u := by
  have h := (norm_sub_norm_le ((Real.log (Real.exp u) : ℂ) *
    zetaSum (Real.exp u) t) (logZetaSum (Real.exp u) t)).trans
      (norm_log_mul_zetaSum_sub_logZetaSum_le t (Real.one_le_exp_iff.mpr hu.le))
  rw [Real.log_exp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.le] at h
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-u)).le
  have he : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
  rw [he] at hmul
  rw [← add_div]
  apply (le_div_iff₀ hu).mpr
  nlinarith

theorem intervalIntegrable_normalized_logZetaSum_div (t : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    IntervalIntegrable (fun u : ℝ =>
      Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ / u) volume 1 L := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hL]
  apply Measure.integrableOn_of_bounded (by simp)
    ((((Real.measurable_exp.comp measurable_neg).mul
      ((measurable_logZetaSum t).comp Real.measurable_exp).norm).div
        measurable_id).aestronglyMeasurable) (M := 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := by linarith [hu.1]
  change ‖Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ / u‖ ≤ 1
  rw [Real.norm_of_nonneg (by positivity)]
  exact (div_le_one hu0).mpr (norm_normalized_logZetaSum_exp_le t hu0.le)

/-- The actual logarithmic average is bounded by the weighted average plus
an explicit `1 + log L` loss, uniformly in height. -/
theorem integral_normalized_zetaSum_exp_le_logSum (t : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    (∫ u : ℝ in 0..L, Real.exp (-u) * ‖zetaSum (Real.exp u) t‖) ≤
      1 + Real.log L +
        ∫ u : ℝ in 1..L, Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ / u := by
  have hsmall : (∫ u : ℝ in 0..1,
      Real.exp (-u) * ‖zetaSum (Real.exp u) t‖) ≤ 1 := by
    calc
      _ ≤ ∫ _u : ℝ in 0..1, (1 : ℝ) := intervalIntegral.integral_mono_on (by norm_num)
        (intervalIntegrable_normalized_zetaSum_exp t 0 1) intervalIntegrable_const
          (fun u _ => norm_normalized_zetaSum_exp_le t u)
      _ = 1 := by simp
  have hinv : IntervalIntegrable (fun u : ℝ => 1 / u) volume 1 L :=
    (continuousOn_const.div continuousOn_id (fun u hu => by
      rw [Set.uIcc_of_le hL] at hu
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1))).intervalIntegrable
  have hlarge := intervalIntegral.integral_mono_on hL
    (intervalIntegrable_normalized_zetaSum_exp t 1 L)
    ((intervalIntegrable_normalized_logZetaSum_div t hL).add hinv)
    (fun u hu => normalized_zetaSum_exp_le_logSum t (by linarith [hu.1]))
  rw [intervalIntegral.integral_add (intervalIntegrable_normalized_logZetaSum_div t hL) hinv,
    integral_one_div_of_pos zero_lt_one (by linarith : 0 < L), div_one] at hlarge
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_normalized_zetaSum_exp t 0 1)
    (intervalIntegrable_normalized_zetaSum_exp t 1 L)]
  linarith

/-- The bounded damping interval reconstructs a reciprocal logarithmic weight. -/
theorem integral_damping_parameter (L : ℝ) {u : ℝ} (hu : 0 < u) :
    (∫ α : ℝ in 0..(1 / 2 : ℝ), Real.exp (-2 * (1 / L + α) * u)) =
      Real.exp (-2 * u / L) * (1 - Real.exp (-u)) / (2 * u) := by
  have hd (α : ℝ) : HasDerivAt
      (fun a : ℝ => -Real.exp (-2 * (1 / L + a) * u) / (2 * u))
        (Real.exp (-2 * (1 / L + α) * u)) α := by
    convert (((Real.hasDerivAt_exp _).comp α
      (((hasDerivAt_id α).const_add (1 / L)).const_mul (-2) |>.mul_const u)).neg.div_const
        (2 * u)) using 1
    simp only [id_eq]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun α _ => hd α)
    ((by fun_prop : Continuous
      (fun α : ℝ => Real.exp (-2 * (1 / L + α) * u))).intervalIntegrable _ _)]
  have he : -2 * (1 / L + 1 / 2) * u = -2 * u / L + -u := by ring
  rw [he, Real.exp_add]
  simp only [add_zero]
  have hz : -2 * (1 / L) * u = -2 * u / L := by ring
  rw [hz]
  ring

theorem reciprocal_le_damping_parameter {L u : ℝ} (hu : 1 ≤ u) (huL : u ≤ L) :
    1 / u ≤ 36 * ∫ α : ℝ in 0..(1 / 2 : ℝ), Real.exp (-2 * (1 / L + α) * u) := by
  have hu0 : 0 < u := by linarith
  have hL : 0 < L := hu0.trans_le huL
  rw [integral_damping_parameter L hu0]
  have hsmall : (1 / 9 : ℝ) ≤ Real.exp (-2 * u / L) := by
    have he2 : Real.exp (2 : ℝ) ≤ 9 := by
      have he1 := Real.exp_one_lt_three
      have he1pos := Real.exp_pos (1 : ℝ)
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith
    have hneg : (1 / 9 : ℝ) ≤ Real.exp (-2 : ℝ) := by
      rw [Real.exp_neg]
      rw [← one_div]
      exact (le_div_iff₀ (Real.exp_pos 2)).mpr (by nlinarith)
    apply hneg.trans (Real.exp_le_exp.mpr ?_)
    exact (le_div_iff₀ hL).mpr (by linarith)
  have hlarge : (1 / 2 : ℝ) ≤ 1 - Real.exp (-u) := by
    have he1 := Real.exp_one_gt_two
    have he : Real.exp (-u) ≤ (1 / 2 : ℝ) := by
      apply (Real.exp_le_exp.mpr (neg_le_neg hu)).trans
      rw [Real.exp_neg]
      rw [← one_div]
      exact (div_le_div_iff₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
    linarith
  have hp := mul_le_mul hsmall hlarge (by norm_num : (0 : ℝ) ≤ 1 / 2) (Real.exp_pos _).le
  calc
    _ ≤ (18 * (Real.exp (-2 * u / L) * (1 - Real.exp (-u)))) / u :=
      div_le_div_of_nonneg_right (by nlinarith) hu0.le
    _ = _ := by ring

/-- Cauchy–Schwarz converts the actual weighted mean square into a damped
first moment. The exponential mass is integrated, not bounded by interval length. -/
theorem integral_damped_logSum_le_sqrt (t : ℝ) {δ L : ℝ} (hδ : 0 < δ) (hL : 1 ≤ L) :
    (∫ u : ℝ in 1..L, Real.exp (-(1 + 2 * δ) * u) * ‖logZetaSum (Real.exp u) t‖) ≤
      Real.sqrt (1 / (2 * δ)) * Real.sqrt
        (∫ u : ℝ, Real.exp (-2 * (1 + δ) * u) * ‖logZetaSum (Real.exp u) t‖ ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc 1 L)
  let f : ℝ → ℝ := fun u => Real.exp (-δ * u)
  let g : ℝ → ℝ := fun u => ‖dampedLogZetaSum t (1 + δ) u‖
  have hf : MemLp f 2 μ := by
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    change ‖Real.exp (-δ * u)‖ ≤ 1
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (by linarith [hu.1])
  have hg : MemLp g 2 μ := (memLp_dampedLogZetaSum_two t (by linarith : 1 < 1 + δ)).norm.restrict _
  have hc := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := μ) (f := f) (g := g)
    (Filter.Eventually.of_forall (fun u => (Real.exp_pos (-δ * u)).le))
    (Filter.Eventually.of_forall (fun u => norm_nonneg (dampedLogZetaSum t (1 + δ) u)))
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
      Real.exp (-2 * (1 + δ) * u) * ‖logZetaSum (Real.exp u) t‖ ^ 2 := by
    dsimp [g, dampedLogZetaSum]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow,
      ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hgbound : (∫ u, g u ^ 2 ∂μ) ≤
      ∫ u : ℝ, Real.exp (-2 * (1 + δ) * u) * ‖logZetaSum (Real.exp u) t‖ ^ 2 := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hgnorm)]
    exact setIntegral_le_integral
      ((memLp_two_iff_integrable_sq ((memLp_dampedLogZetaSum_two t
        (by linarith : 1 < 1 + δ)).norm.aestronglyMeasurable)).mp
          (memLp_dampedLogZetaSum_two t (by linarith : 1 < 1 + δ)).norm)
      (Filter.Eventually.of_forall (fun u => sq_nonneg (g u)))
  have hfg (u : ℝ) : f u * g u =
      Real.exp (-(1 + 2 * δ) * u) * ‖logZetaSum (Real.exp u) t‖ := by
    dsimp [f, g, dampedLogZetaSum]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hc' : (∫ u, f u * g u ∂μ) ≤
      Real.sqrt (∫ u, f u ^ 2 ∂μ) * Real.sqrt (∫ u, g u ^ 2 ∂μ) := by
    simpa only [Real.sqrt_eq_rpow, one_div, Real.rpow_two] using hc
  rw [intervalIntegral.integral_of_le hL]
  simp_rw [hfg] at hc'
  exact hc'.trans (mul_le_mul (Real.sqrt_le_sqrt hfbound) (Real.sqrt_le_sqrt hgbound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem integrable_damping_rectangle (t : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    Integrable (fun p : ℝ × ℝ =>
      Real.exp (-(1 + 2 * (1 / L + p.2)) * p.1) * ‖logZetaSum (Real.exp p.1) t‖)
      ((volume.restrict (Set.Ioc 1 L)).prod (volume.restrict (Set.Ioc 0 (1 / 2 : ℝ)))) := by
  rw [Measure.prod_restrict]
  apply Measure.integrableOn_of_bounded (by simp; finiteness)
    (((by fun_prop : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(1 + 2 * (1 / L + p.2)) * p.1))).mul
        (((measurable_logZetaSum t).comp
          (Real.measurable_exp.comp measurable_fst)).norm)).aestronglyMeasurable) (M := L)
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
  change ‖Real.exp (-(1 + 2 * (1 / L + p.2)) * p.1) *
    ‖logZetaSum (Real.exp p.1) t‖‖ ≤ L
  rw [Real.norm_of_nonneg (by positivity)]
  have hL0 : 0 < L := by linarith
  have hp0 : 0 ≤ p.1 := by linarith [hp.1.1]
  have hδ : 0 ≤ 1 / L + p.2 := add_nonneg (one_div_nonneg.mpr hL0.le) hp.2.1.le
  have he : -(1 + 2 * (1 / L + p.2)) * p.1 =
      -2 * (1 / L + p.2) * p.1 + -p.1 := by ring
  rw [he, Real.exp_add, mul_assoc]
  calc
    _ ≤ 1 * p.1 := mul_le_mul
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hp0))
      (norm_normalized_logZetaSum_exp_le t hp0) (by positivity) (by norm_num)
    _ ≤ L := by simpa using hp.1.2

/-- A finite, absolutely integrable parameter exchange for the actual weighted
sum. This is the reciprocal-weight reconstruction used in mean-value assembly. -/
theorem integral_normalized_logSum_le_damping_average (t : ℝ) {L : ℝ} (hL : 1 ≤ L) :
    (∫ u : ℝ in 1..L, Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ / u) ≤
      36 * ∫ α : ℝ in 0..(1 / 2 : ℝ),
        ∫ u : ℝ in 1..L, Real.exp (-(1 + 2 * (1 / L + α)) * u) *
          ‖logZetaSum (Real.exp u) t‖ := by
  let F : ℝ → ℝ → ℝ := fun u α =>
    Real.exp (-(1 + 2 * (1 / L + α)) * u) * ‖logZetaSum (Real.exp u) t‖
  have hF := integrable_damping_rectangle t hL
  have hinner : IntervalIntegrable (fun u => ∫ α : ℝ in 0..(1 / 2 : ℝ), F u α) volume 1 L := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hL]
    simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      using hF.integral_prod_left
  have hbound := intervalIntegral.integral_mono_on hL
    (intervalIntegrable_normalized_logZetaSum_div t hL) (hinner.const_mul 36) (fun u hu => by
      have hrec := mul_le_mul_of_nonneg_left (reciprocal_le_damping_parameter hu.1 hu.2)
        (show 0 ≤ Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖ by positivity)
      have hfactor : (∫ α : ℝ in 0..(1 / 2 : ℝ), F u α) =
          (Real.exp (-u) * ‖logZetaSum (Real.exp u) t‖) *
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
  have hswap : (∫ u : ℝ in 1..L, ∫ α : ℝ in 0..(1 / 2 : ℝ), F u α) =
      ∫ α : ℝ in 0..(1 / 2 : ℝ), ∫ u : ℝ in 1..L, F u α := by
    simp_rw [intervalIntegral.integral_of_le hL,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact integral_integral_swap hF
  rwa [hswap] at hbound

theorem norm_shifted_zeta_le_reciprocal (σ t y : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ≤ 1 + 1 / (σ - 1) := by
  have h := (norm_tsum_logFrequency_le (zetaPhaseCoeff σ t)
    (summable_norm_zetaPhaseCoeff σ t hσ) y).trans (tsum_norm_zetaPhaseCoeff_le σ t hσ)
  rwa [tsum_zetaPhaseCoeff_phase σ t y hσ] at h

/-- Explicit near/far majorant after Cauchy–Schwarz. The minimum retains both
the original-line maximum and the absolutely convergent series bound. -/
def meanValueDampingBound (L Z α : ℝ) : ℝ :=
  Real.sqrt (1 / (2 * (1 / L + α))) * Real.sqrt
    ((min (Z + (1 + L) * (4 * α / (Real.pi * L))) (1 + 1 / (1 / L + α))) ^ 2 *
      (Real.log 4 + 4) ^ 2 / (2 * (1 / L + α)) +
        (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4) *
          (2 / L + 4 / ((1 / L + α) ^ 3 * L ^ 2))))

theorem continuousOn_meanValueDampingBound {L : ℝ} (hL : 0 < L) (Z : ℝ) :
    ContinuousOn (meanValueDampingBound L Z) (Set.Icc 0 (1 / 2 : ℝ)) := by
  intro α hα
  have hδ : 0 < 1 / L + α := add_pos_of_pos_of_nonneg (one_div_pos.mpr hL) hα.1
  apply ContinuousAt.continuousWithinAt
  unfold meanValueDampingBound
  fun_prop (disch := positivity)

/-- One actual source maximizer controls every damped first moment used in
the parameter integral. No maximum or mean-square estimate is assumed. -/
theorem exists_maximizingTwist_damped_first_moment {x : ℝ}
    (hx : 1 < x) (hxlog : 8 ≤ Real.log x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ∀ α : ℝ, 0 < α → α ≤ 1 / 2 →
        (∫ u : ℝ in 1..Real.log x,
          Real.exp (-(1 + 2 * (1 / Real.log x + α)) * u) * ‖logZetaSum (Real.exp u) t‖) ≤
            meanValueDampingBound (Real.log x) ‖riemannZeta (twistZetaPoint x t t₀)‖ α := by
  obtain ⟨t₀, ht₀, hmax, hright⟩ := exists_maximizingTwist_rightward_bound hx t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  intro α hα hαtop
  have hL : 0 < Real.log x := Real.log_pos hx
  have hδ : 0 < 1 / Real.log x + α := add_pos (one_div_pos.mpr hL) hα
  have hδtop : 1 / Real.log x + α ≤ 1 := by
    have h : 1 / Real.log x ≤ (1 / 8 : ℝ) :=
      (div_le_div_iff₀ hL (by norm_num)).mpr (by simpa using hxlog)
    linarith
  have hσ : 1 < 1 + (1 / Real.log x + α) := by linarith
  have hlocal (u : ℝ) (hu : |u| ≤ Real.log x / 2) :
      ‖riemannZeta (((1 + (1 / Real.log x + α) : ℝ) : ℂ) + ((u - t : ℝ) : ℂ) * I)‖ ≤
        min (‖riemannZeta (twistZetaPoint x t t₀)‖ +
          (1 + Real.log x) * (4 * α / (Real.pi * Real.log x))) (1 + 1 / (1 / Real.log x + α)) := by
    apply le_min
    · simpa only [add_assoc] using hright α hα u hu
    · simpa only [add_sub_cancel_left] using
        norm_shifted_zeta_le_reciprocal (1 + (1 / Real.log x + α)) t u hσ
  have hms := zeta_deriv_quotient_mean_square_le (1 + (1 / Real.log x + α)) t
    (Real.log x / 2)
    (min (‖riemannZeta (twistZetaPoint x t t₀)‖ +
      (1 + Real.log x) * (4 * α / (Real.pi * Real.log x))) (1 + 1 / (1 / Real.log x + α)))
      hσ (by linarith) (by linarith) hlocal
  rw [integral_zeta_deriv_quotient_sq_eq_logSum_sq t hσ, add_sub_cancel_left] at hms
  have htail : 1 / (Real.log x / 2) +
      1 / ((1 / Real.log x + α) ^ 3 * (Real.log x / 2) ^ 2) =
        2 / Real.log x + 4 / ((1 / Real.log x + α) ^ 3 * (Real.log x) ^ 2) := by
    field_simp [hL.ne', hδ.ne']
    ring
  rw [htail] at hms
  exact (integral_damped_logSum_le_sqrt t hδ (by linarith : 1 ≤ Real.log x)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hms) (Real.sqrt_nonneg _))

/-- Pointwise mean-value control from the actual maximizing zeta value.
All smoothing, convergence, parameter exchange and spectral estimates are
consumed; evaluating the remaining elementary parameter integral is separate. -/
theorem exists_maximizingTwist_parameter_mean_bound {x : ℝ}
    (hx : 1 < x) (hxlog : 8 ≤ Real.log x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ‖zetaSum x t‖ / x ≤
        2048 / Real.log x * (1 + Real.log (Real.log x) +
          36 * ∫ α : ℝ in 0..(1 / 2 : ℝ), meanValueDampingBound (Real.log x)
            ‖riemannZeta (twistZetaPoint x t t₀)‖ α) + 952321 / Real.log x := by
  obtain ⟨t₀, ht₀, hmax, hmoment⟩ := exists_maximizingTwist_damped_first_moment hx hxlog t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  have hL : 1 ≤ Real.log x := by linarith
  have hF := (integrable_damping_rectangle t hL).integral_prod_right
  have hi : IntervalIntegrable (fun α : ℝ => ∫ u : ℝ in 1..Real.log x,
      Real.exp (-(1 + 2 * (1 / Real.log x + α)) * u) * ‖logZetaSum (Real.exp u) t‖)
        volume 0 (1 / 2) := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simpa only [intervalIntegral.integral_of_le hL] using hF
  have hparam := intervalIntegral.integral_mono_ae_restrict (by norm_num : (0 : ℝ) ≤ 1 / 2)
    hi ((continuousOn_meanValueDampingBound (Real.log_pos hx)
      ‖riemannZeta (twistZetaPoint x t t₀)‖).intervalIntegrable_of_Icc (by norm_num))
    (by
      rw [← restrict_Ioc_eq_restrict_Icc]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact hmoment α hα.1 hα.2)
  have hweight := integral_normalized_logSum_le_damping_average t hL
  have havg := integral_normalized_zetaSum_exp_le_logSum t hL
  have hwhole : (∫ u : ℝ in 0..Real.log x, Real.exp (-u) * ‖zetaSum (Real.exp u) t‖) ≤
      1 + Real.log (Real.log x) + 36 * ∫ α : ℝ in 0..(1 / 2 : ℝ),
        meanValueDampingBound (Real.log x) ‖riemannZeta (twistZetaPoint x t t₀)‖ α := by
    linarith
  exact (norm_normalized_zetaSum_le_log_average t hx).trans
    (add_le_add (mul_le_mul_of_nonneg_left hwhole
      (show 0 ≤ 2048 / Real.log x by positivity)) le_rfl)

private theorem sqrt_spectral_majorant_le {C K M δ L : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ) (hL : 0 < L)
    (hδL : 1 ≤ δ * L) :
    Real.sqrt (1 / (2 * δ)) * Real.sqrt
      (M ^ 2 * C ^ 2 / (2 * δ) + K * (2 / L + 4 / (δ ^ 3 * L ^ 2))) ≤
        (C + K + 2) * (M / δ + 1 + 1 / (δ ^ 2 * L)) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 1 / (2 * δ))]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  let B := C + K + 2
  have hBC : (C / 2) ^ 2 ≤ B ^ 2 := by
    have h := show C / 2 ≤ B by dsimp [B]; linarith
    exact pow_le_pow_left₀ (by positivity) h 2
  have hBK : 2 * K ≤ B ^ 2 := by
    have h := sq_nonneg (K + 1)
    have hle : K + 1 ≤ B := by dsimp [B]; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ K + 1) hle 2
    nlinarith
  have hfrac : K / (δ * L) ≤ K := (div_le_iff₀ (mul_pos hδ hL)).mpr
    (by nlinarith)
  have heq : 1 / (2 * δ) *
      (M ^ 2 * C ^ 2 / (2 * δ) + K * (2 / L + 4 / (δ ^ 3 * L ^ 2))) =
        (M / δ) ^ 2 * (C / 2) ^ 2 + K / (δ * L) + 2 * K * (1 / (δ ^ 2 * L)) ^ 2 := by
    field_simp
    ring
  rw [heq]
  have hfirst := mul_le_mul_of_nonneg_left hBC (sq_nonneg (M / δ))
  have hlast := mul_le_mul_of_nonneg_right hBK (sq_nonneg (1 / (δ ^ 2 * L)))
  have hpoly : (M / δ) ^ 2 + 1 + (1 / (δ ^ 2 * L)) ^ 2 ≤
      (M / δ + 1 + 1 / (δ ^ 2 * L)) ^ 2 := by
    have ha : 0 ≤ M / δ := div_nonneg hM hδ.le
    have hb : 0 ≤ 1 / (δ ^ 2 * L) := by positivity
    nlinarith [mul_nonneg ha hb]
  calc
    _ ≤ B ^ 2 * ((M / δ) ^ 2 + 1 + (1 / (δ ^ 2 * L)) ^ 2) := by nlinarith
    _ ≤ B ^ 2 * (M / δ + 1 + 1 / (δ ^ 2 * L)) ^ 2 :=
      mul_le_mul_of_nonneg_left hpoly (sq_nonneg B)
    _ = _ := by dsimp [B]; ring

/-- One absolute coefficient for the elementary parameter majorant. -/
def meanValueAssemblyConstant : ℝ :=
  (Real.log 4 + 4) + (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4)) + 2

theorem meanValueAssemblyConstant_pos : 0 < meanValueAssemblyConstant := by
  unfold meanValueAssemblyConstant
  positivity

/-- The near/far square-root expression reduces to one minimum and an
integrable reciprocal-square error on the actual damping range. -/
theorem meanValueDampingBound_le {L Z α : ℝ} (hL : 2 ≤ L) (hZ : 0 ≤ Z)
    (hα : 0 ≤ α) (hαtop : α ≤ 1 / 2) :
    meanValueDampingBound L Z α ≤ meanValueAssemblyConstant *
      (min (Z + 4) (2 / (1 / L + α)) / (1 / L + α) + 1 +
        1 / ((1 / L + α) ^ 2 * L)) := by
  have hL0 : 0 < L := by linarith
  have hδ : 0 < 1 / L + α := add_pos_of_pos_of_nonneg (one_div_pos.mpr hL0) hα
  have hδtop : 1 / L + α ≤ 1 := by
    have h : 1 / L ≤ (1 / 2 : ℝ) :=
      (div_le_div_iff₀ hL0 (by norm_num)).mpr (by simpa using hL)
    linarith
  have hδL : 1 ≤ (1 / L + α) * L := by
    rw [add_mul, one_div_mul_cancel hL0.ne']
    nlinarith
  have hmin0 : 0 ≤ min (Z + (1 + L) * (4 * α / (Real.pi * L)))
      (1 + 1 / (1 / L + α)) := by positivity
  have hmajor := sqrt_spectral_majorant_le
    (show 0 ≤ Real.log 4 + 4 by positivity)
    (show 0 ≤ (2 * Real.pi)⁻¹ * (192 * Real.sqrt Real.pi * Real.exp (5 / 4)) by positivity)
    hmin0 hδ hL0 hδL
  have hmin : min (Z + (1 + L) * (4 * α / (Real.pi * L))) (1 + 1 / (1 / L + α)) ≤
      min (Z + 4) (2 / (1 / L + α)) := by
    apply le_min
    · apply (min_le_left _ _).trans
      have hpi : 2 ≤ Real.pi := Real.two_le_pi
      have hbound : (1 + L) * (4 * α / (Real.pi * L)) ≤ 4 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (mul_pos Real.pi_pos hL0)).mpr
        have h := mul_le_mul_of_nonneg_right hpi hL0.le
        nlinarith [mul_le_mul_of_nonneg_left hαtop (by linarith : 0 ≤ L)]
      linarith
    · apply (min_le_right _ _).trans
      apply (le_div_iff₀ hδ).mpr
      have he : (1 + 1 / (1 / L + α)) * (1 / L + α) = 1 / L + α + 1 := by field_simp
      rw [he]
      linarith
  change Real.sqrt _ * Real.sqrt _ ≤ _
  have hmajor' : meanValueDampingBound L Z α ≤ meanValueAssemblyConstant *
      (min (Z + (1 + L) * (4 * α / (Real.pi * L))) (1 + 1 / (1 / L + α)) /
        (1 / L + α) + 1 + 1 / ((1 / L + α) ^ 2 * L)) := by
    simpa only [meanValueDampingBound, meanValueAssemblyConstant, mul_assoc] using hmajor
  exact hmajor'.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (div_le_div_of_nonneg_right hmin hδ.le) le_rfl) le_rfl)
    meanValueAssemblyConstant_pos.le)

theorem integral_reciprocal_sq (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ u : ℝ in a..b, c / u ^ 2) = c / a - c / b := by
  have hd (u : ℝ) (hu : u ∈ Set.uIcc a b) :
      HasDerivAt (fun v : ℝ => -c / v) (c / u ^ 2) u := by
    rw [Set.uIcc_of_le hab] at hu
    have hu0 := ha.trans_le hu.1
    convert (hasDerivAt_const u (-c)).div (hasDerivAt_id u) hu0.ne' using 1
    simp
  have hi : IntervalIntegrable (fun u : ℝ => c / u ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    have hu0 := ha.trans_le hu.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  ring

/-- Exact logarithmic splitting at `2/R` evaluates the decisive minimum.
The reciprocal-square part has a finite mass even at an unbounded upper cutoff. -/
theorem integral_min_reciprocal_le {a b R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hac : a ≤ 2 / R) (hcb : 2 / R ≤ b) :
    (∫ u : ℝ in a..b, min R (2 / u) / u) ≤ R * (1 + Real.log (2 / (a * R))) := by
  let c := 2 / R
  have hc : 0 < c := by dsimp [c]; positivity
  have hb : 0 < b := hc.trans_le hcb
  have hcont : ContinuousOn (fun u : ℝ => min R (2 / u) / u) (Set.Icc a b) := by
    intro u hu
    have hu0 := ha.trans_le hu.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hleftInt : IntervalIntegrable (fun u : ℝ => min R (2 / u) / u) volume a c :=
    (hcont.mono (Set.Icc_subset_Icc le_rfl hcb)).intervalIntegrable_of_Icc hac
  have hrightInt : IntervalIntegrable (fun u : ℝ => min R (2 / u) / u) volume c b :=
    (hcont.mono (Set.Icc_subset_Icc hac le_rfl)).intervalIntegrable_of_Icc hcb
  have hleftMajor : IntervalIntegrable (fun u : ℝ => R / u) volume a c := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hac] at hu
    have hu0 := ha.trans_le hu.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hrightMajor : IntervalIntegrable (fun u : ℝ => 2 / u ^ 2) volume c b := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le hcb] at hu
    have hu0 := hc.trans_le hu.1
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hleft := intervalIntegral.integral_mono_on hac hleftInt hleftMajor (fun u hu =>
    div_le_div_of_nonneg_right (min_le_left _ _) (ha.le.trans hu.1))
  have hright := intervalIntegral.integral_mono_on hcb hrightInt hrightMajor (fun u hu => by
    calc
      _ ≤ (2 / u) / u := div_le_div_of_nonneg_right (min_le_right _ _) (hc.le.trans hu.1)
      _ = 2 / u ^ 2 := by ring)
  have hleftEq : (∫ u : ℝ in a..c, R / u) = R * Real.log (c / a) := by
    simp_rw [div_eq_mul_one_div R]
    rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos ha hc]
  rw [hleftEq] at hleft
  rw [integral_reciprocal_sq 2 hc hcb] at hright
  have hquot : 2 / c = R := by dsimp [c]; field_simp
  have hlog : c / a = 2 / (a * R) := by dsimp [c]; ring
  rw [hquot] at hright
  rw [hlog] at hleft
  rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
  have hpos : 0 ≤ 2 / b := by positivity
  nlinarith

/-- Evaluation of the remaining parameter integral, with its logarithmic
dependence on the actual maximum retained. -/
theorem integral_meanValueDampingBound_le {L Z : ℝ} (hL : 8 ≤ L) (hZ : 0 ≤ Z)
    (hZtop : Z ≤ 1 + L) :
    (∫ α : ℝ in 0..(1 / 2 : ℝ), meanValueDampingBound L Z α) ≤
      meanValueAssemblyConstant * ((Z + 4) * (1 + Real.log (2 * L / (Z + 4))) + 2) := by
  let a := 1 / L
  let R := Z + 4
  have hL0 : 0 < L := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hR : 0 < R := by dsimp [R]; linarith
  have hR4 : 4 ≤ R := by dsimp [R]; linarith
  have hRtop : R ≤ 2 * L := by dsimp [R]; linarith
  have hac : a ≤ 2 / R := by
    dsimp [a]
    exact (div_le_div_iff₀ hL0 hR).mpr (by simpa using hRtop)
  have hcb : 2 / R ≤ a + 1 / 2 := by
    have h : 2 / R ≤ (1 / 2 : ℝ) := (div_le_iff₀ hR).mpr (by linarith)
    linarith
  let F : ℝ → ℝ := fun α => min R (2 / (a + α)) / (a + α)
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
      ∫ u : ℝ in a..a + 1 / 2, min R (2 / u) / u := by
    simpa only [F, add_zero] using intervalIntegral.integral_comp_add_left
      (a := 0) (b := 1 / 2) (fun u : ℝ => min R (2 / u) / u) a
  have hFbound : (∫ α : ℝ in 0..(1 / 2 : ℝ), F α) ≤
      R * (1 + Real.log (2 * L / R)) := by
    rw [hFeq]
    convert integral_min_reciprocal_le ha hR hac hcb using 1
    dsimp [a]
    congr 3
    field_simp
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
  have hbound := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ((continuousOn_meanValueDampingBound hL0 Z).intervalIntegrable_of_Icc (by norm_num))
    (((hF.add intervalIntegrable_const).add hG).const_mul meanValueAssemblyConstant)
    (fun α hα => meanValueDampingBound_le (by linarith : 2 ≤ L) hZ hα.1 hα.2)
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hF.add intervalIntegrable_const) hG,
    intervalIntegral.integral_add hF intervalIntegrable_const] at hbound
  norm_num only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (by linarith) meanValueAssemblyConstant_pos.le)

/-- An unconditional maximum-form mean-value theorem for the actual phase
sum, with explicit height-independent constants and no residual analytic integral. -/
theorem exists_maximizingTwist_mean_value_bound {x : ℝ}
    (hx : 1 < x) (hxlog : 8 ≤ Real.log x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ‖zetaSum x t‖ / x ≤ 2048 / Real.log x * (1 + Real.log (Real.log x) +
        36 * meanValueAssemblyConstant *
          ((‖riemannZeta (twistZetaPoint x t t₀)‖ + 4) *
            (1 + Real.log (2 * Real.log x / (‖riemannZeta (twistZetaPoint x t t₀)‖ + 4))) + 2)) +
              952321 / Real.log x := by
  obtain ⟨t₀, ht₀, hmax, hmean⟩ := exists_maximizingTwist_parameter_mean_bound hx hxlog t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  have hL : 0 < Real.log x := Real.log_pos hx
  have hZtop : ‖riemannZeta (twistZetaPoint x t t₀)‖ ≤ 1 + Real.log x := by
    have h := norm_shifted_zeta_le_reciprocal (1 + 1 / Real.log x) t t₀
      (by linarith [one_div_pos.mpr hL])
    simpa only [twistZetaPoint, add_sub_cancel_left, one_div_one_div] using h
  have hi := integral_meanValueDampingBound_le hxlog (norm_nonneg _) hZtop
  apply hmean.trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ 2048 / Real.log x by positivity)
  have h := mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 36)
  nlinarith

private theorem logWeight_mono {A a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbA : b ≤ A) :
    a * (1 + Real.log (A / a)) ≤ b * (1 + Real.log (A / b)) := by
  have hb := ha.trans_le hab
  have hA := hb.trans_le hbA
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have hmul := mul_le_mul_of_nonneg_left hlog ha.le
  have hcancel : a * (b / a - 1) = b - a := by field_simp
  rw [hcancel] at hmul
  have hnonneg : 0 ≤ Real.log (A / b) := Real.log_nonneg ((one_le_div hb).mpr hbA)
  have hsplit : Real.log (A / a) = Real.log (A / b) + Real.log (b / a) := by
    rw [Real.log_div hA.ne' ha.ne', Real.log_div hA.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    ring
  rw [hsplit]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) hnonneg]

private theorem logWeight_add_le {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) :
    (a + b) * (1 + Real.log (A / (a + b))) ≤
      a * (1 + Real.log (A / a)) + b * (1 + Real.log (A / b)) := by
  have hab : 0 < a + b := add_pos ha hb
  have hleft := Real.log_le_log (div_pos hA hab)
    (div_le_div_of_nonneg_left hA.le ha (by linarith : a ≤ a + b))
  have hright := Real.log_le_log (div_pos hA hab)
    (div_le_div_of_nonneg_left hA.le hb (by linarith : b ≤ a + b))
  nlinarith [mul_le_mul_of_nonneg_left hleft ha.le, mul_le_mul_of_nonneg_left hright hb.le]

private theorem logWeight_euler_bound {L Z A M : ℝ} (hL : 1 ≤ L) (hZ : 0 < Z)
    (hA : 0 ≤ A) (hM : A + 2 ≤ M) (hZE : Z ≤ (1 + L) * Real.exp (A - M)) :
    (Z + 4) * (1 + Real.log (2 * L / (Z + 4))) ≤
      4 * L * Real.exp A * ((M + 1) * Real.exp (-M)) + 4 * (1 + Real.log L) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 ≤ M := by linarith
  let U := (1 + L) * Real.exp (A - M)
  have hU : 0 < U := by dsimp [U]; positivity
  have he : Real.exp (A - M) ≤ 1 / 2 := by
    apply (Real.exp_le_exp.mpr (show A - M ≤ -2 by linarith)).trans
    rw [Real.exp_neg, ← one_div]
    apply (div_le_div_iff₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hUL : U ≤ L := by
    have hm := mul_le_mul_of_nonneg_left he (by linarith : 0 ≤ 1 + L)
    dsimp [U]
    linarith
  have hmono := logWeight_mono hZ hZE (show U ≤ 2 * L by linarith)
  have hlogU : 1 + Real.log (2 * L / U) ≤ M + 2 := by
    have hratio : 0 < 2 * L / (1 + L) := by positivity
    have hr : 2 * L / (1 + L) ≤ 2 := (div_le_iff₀ (by linarith : 0 < 1 + L)).mpr (by linarith)
    have hlog := (Real.log_le_log hratio hr).trans (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2))
    have hidentity : Real.log (2 * L / U) = Real.log (2 * L / (1 + L)) - (A - M) := by
      dsimp [U]
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_exp, Real.log_div (by positivity) (by positivity)]
      ring
    rw [hidentity]
    linarith
  have hUbound : U * (1 + Real.log (2 * L / U)) ≤
      4 * L * Real.exp A * ((M + 1) * Real.exp (-M)) := by
    calc
      _ ≤ U * (M + 2) := mul_le_mul_of_nonneg_left hlogU hU.le
      _ = (1 + L) * Real.exp A * Real.exp (-M) * (M + 2) := by dsimp [U]; rw [Real.exp_sub, Real.exp_neg]; ring
      _ ≤ (2 * L) * Real.exp A * Real.exp (-M) * (2 * (M + 1)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith : 1 + L ≤ 2 * L) (Real.exp_pos A).le)
            (Real.exp_pos (-M)).le
        · linarith
        · linarith
        · positivity
      _ = _ := by ring
  have hfour : 4 * (1 + Real.log (2 * L / 4)) ≤ 4 * (1 + Real.log L) := by
    have hlog := Real.log_le_log (by positivity : 0 < 2 * L / 4) (show 2 * L / 4 ≤ L by linarith)
    linarith
  exact (logWeight_add_le (by positivity : 0 < 2 * L) hZ (by norm_num)).trans
    (add_le_add (hmono.trans hUbound) hfour)

/-- Absolute coefficient for ordinary mean-value control by prime distance. -/
def ordinaryHalaszConstant : ℝ :=
  1000000 * (1 + meanValueAssemblyConstant) * Real.exp (4 * (Real.log 4 + 4) + 2)

theorem ordinaryHalaszConstant_pos : 0 < ordinaryHalaszConstant := by
  unfold ordinaryHalaszConstant
  positivity [meanValueAssemblyConstant_pos]

/-- Ordinary Halász-type control at the actual source maximizer. This consumes
the proved Euler-distance bound, not a supplied small-distance assumption. -/
theorem exists_maximizingTwist_prime_distance_mean_bound {x : ℝ}
    (hx : 1 < x) (hxlog : 8 ≤ Real.log x) (t : ℝ) :
    ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
      (∀ u : ℝ, |u| ≤ Real.log x →
        ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
      ‖zetaSum x t‖ / x ≤ ordinaryHalaszConstant *
        ((primePhaseDistance x (t - t₀) + 1) * Real.exp (-primePhaseDistance x (t - t₀)) +
          (1 + Real.log (Real.log x)) / Real.log x) := by
  obtain ⟨t₀, ht₀, hmax, hmean⟩ := exists_maximizingTwist_mean_value_bound hx hxlog t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  let L := Real.log x
  let Z := ‖riemannZeta (twistZetaPoint x t t₀)‖
  let M := primePhaseDistance x (t - t₀)
  let A := 4 * (Real.log 4 + 4)
  let B := meanValueAssemblyConstant
  let V := (M + 1) * Real.exp (-M)
  let W := (1 + Real.log L) / L
  have hL : 8 ≤ L := hxlog
  have hL0 : 0 < L := Real.log_pos hx
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := primePhaseDistance_nonneg _ _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 < B := meanValueAssemblyConstant_pos
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hD : ordinaryHalaszConstant = 1000000 * (1 + B) * Real.exp (A + 2) := rfl
  have hDexp : Real.exp (A + 2) ≤ ordinaryHalaszConstant := by
    rw [hD]
    have hp := Real.exp_pos (A + 2)
    nlinarith
  by_cases hsmall : M ≤ A + 2
  · have he := mul_le_mul_of_nonneg_right ((Real.exp_le_exp.mpr hsmall).trans hDexp)
      (Real.exp_pos (-M)).le
    have heq : Real.exp M * Real.exp (-M) = 1 := by rw [← Real.exp_add]; simp
    rw [heq] at he
    have hmul : Real.exp (-M) ≤ V := by dsimp [V]; nlinarith [Real.exp_pos (-M)]
    have hunit : ‖zetaSum x t‖ / x ≤ 1 :=
      (div_le_one (zero_lt_one.trans hx)).mpr (norm_zetaSum_le (by linarith) t)
    change ‖zetaSum x t‖ / x ≤ ordinaryHalaszConstant * (V + W)
    exact hunit.trans (he.trans (mul_le_mul_of_nonneg_left (by linarith) ordinaryHalaszConstant_pos.le))
  have hZ : 0 < Z := by
    apply norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re ?_)
    rw [twistZetaPoint_re]
    linarith [one_div_pos.mpr hL0]
  have hZE : Z ≤ (1 + L) * Real.exp (A - M) :=
    norm_twistZeta_le_primePhaseDistance x t t₀ hx (by linarith)
  have hweight := logWeight_euler_bound (by linarith : 1 ≤ L) hZ hA (le_of_not_ge hsmall) hZE
  have hweight' : (Z + 4) * (1 + Real.log (2 * L / (Z + 4))) + 2 ≤
      4 * L * Real.exp A * V + 6 * (1 + Real.log L) := by
    dsimp [V]
    linarith
  have hmid : ‖zetaSum x t‖ / x ≤
      294912 * B * Real.exp A * V + (954369 + 442368 * B) * W := by
    calc
      _ ≤ 2048 / L * (1 + Real.log L + 36 * B *
          ((Z + 4) * (1 + Real.log (2 * L / (Z + 4))) + 2)) + 952321 / L := hmean
      _ ≤ 2048 / L * (1 + Real.log L + 36 * B *
          (4 * L * Real.exp A * V + 6 * (1 + Real.log L))) + 952321 / L := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left hweight' (by positivity)))
            (by positivity : 0 ≤ 2048 / L)) le_rfl
      _ = 294912 * B * Real.exp A * V + (2048 + 442368 * B) * W + 952321 / L := by
        dsimp [W]
        field_simp
        ring
      _ ≤ _ := by
        have hi : 1 / L ≤ W := div_le_div_of_nonneg_right (by linarith) hL0.le
        have hi' : 952321 / L ≤ 952321 * W := by
          simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hi (by norm_num : (0 : ℝ) ≤ 952321)
        nlinarith
  have hE1 : 1 ≤ Real.exp (A + 2) := Real.one_le_exp_iff.mpr (by linarith)
  have hDA : 294912 * B * Real.exp A ≤ ordinaryHalaszConstant := by
    rw [hD]
    calc
      _ ≤ 1000000 * (1 + B) * Real.exp A := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hDW : 954369 + 442368 * B ≤ ordinaryHalaszConstant := by
    rw [hD]
    have h := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ 1000000 * (1 + B) by positivity)
    nlinarith
  change ‖zetaSum x t‖ / x ≤ ordinaryHalaszConstant * (V + W)
  apply hmid.trans
  nlinarith [mul_le_mul_of_nonneg_right hDA hV, mul_le_mul_of_nonneg_right hDW hW]

theorem primePhaseDistance_le_reciprocal_primes (x τ : ℝ) :
    primePhaseDistance x τ ≤ 2 * ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
  rw [primePhaseDistance, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hre := Complex.re_le_norm (-zetaTerm τ p)
  rw [Complex.neg_re, norm_neg, norm_zetaTerm τ hprime.pos] at hre
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (by linarith :
    1 - (zetaTerm τ p).re ≤ 2) (Nat.cast_nonneg p)

/-- The crude distance estimate used to invert the ordinary mean-value bound. -/
theorem primePhaseDistance_add_one_le_log (x τ : ℝ) (hx : 1 < x) (hxlog : 8 ≤ Real.log x) :
    primePhaseDistance x τ + 1 ≤ (4 * (Real.log 4 + 4) + 5) * Real.log (Real.log x) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hlogone : 1 ≤ Real.log (Real.log x) :=
    (Real.le_log_iff_exp_le hL0).mpr (by linarith [Real.exp_one_lt_three])
  have hprime := sum_prime_reciprocal_le hx (by linarith : 1 ≤ Real.log x)
  have hdist := primePhaseDistance_le_reciprocal_primes x τ
  have hlog : Real.log (1 + Real.log x) ≤ 1 + Real.log (Real.log x) := by
    have h := Real.log_le_log (by positivity : 0 < 1 + Real.log x)
      (show 1 + Real.log x ≤ 2 * Real.log x by linarith)
    rw [Real.log_mul (by norm_num) hL0.ne'] at h
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hC : 0 ≤ 4 * (Real.log 4 + 4) + 3 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlogone hC]

/-- The ordinary error is smaller than half the smallest allowed large sum,
at an absolute threshold independent of the height and of `N`. -/
theorem exists_ordinary_mean_error_threshold :
    ∃ L₀ : ℝ, 8 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ordinaryHalaszConstant * ((1 + Real.log L) / L) ≤ 1 / (2 * L ^ (1 / 100 : ℝ)) := by
  have hD := ordinaryHalaszConstant_pos
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).bound
    (show 0 < 1 / (4 * ordinaryHalaszConstant) by positivity)
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).eventually_ge_atTop
    (4 * ordinaryHalaszConstant)
  have hevent : ∀ᶠ L : ℝ in Filter.atTop,
      8 ≤ L ∧ ordinaryHalaszConstant * ((1 + Real.log L) / L) ≤
        1 / (2 * L ^ (1 / 100 : ℝ)) := by
    filter_upwards [hlog, hpow, Filter.eventually_ge_atTop (8 : ℝ)] with L hlogL hpowL hL
    have hL0 : 0 < L := by linarith
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    simp only [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (Real.rpow_nonneg hL0.le _)] at hlogL
    have hsmall : ordinaryHalaszConstant * (1 + Real.log L) ≤ L ^ (99 / 100 : ℝ) / 2 := by
      have hmul := (le_div_iff₀ (show 0 < 4 * ordinaryHalaszConstant by positivity)).mp
        (show Real.log L ≤ L ^ (99 / 100 : ℝ) / (4 * ordinaryHalaszConstant) by
          simpa only [one_div_mul_eq_div] using hlogL)
      nlinarith
    have hpowid : L ^ (99 / 100 : ℝ) * L ^ (1 / 100 : ℝ) = L := by
      rw [← Real.rpow_add hL0]
      norm_num
    refine ⟨hL, ?_⟩
    apply (le_div_iff₀ (show 0 < 2 * L ^ (1 / 100 : ℝ) by positivity)).mpr
    have hmul := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 2 * L ^ (1 / 100 : ℝ) by positivity)
    have hdesired : ordinaryHalaszConstant * (1 + Real.log L) * (2 * L ^ (1 / 100 : ℝ)) ≤ L := by
      nlinarith [hpowid]
    have h := (div_le_one hL0).mpr hdesired
    convert h using 1
    ring
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max L₁ 8, le_max_right _ _, fun L hL => (hL₁ L ((le_max_left _ _).trans hL)).2⟩

/-- The prime-distance conclusion of source Lemma 2.2, with its exact leading
coefficient and absolute threshold. The source maximizer is produced from the
actual large sum, rather than assuming its distance is small. -/
theorem exists_large_sum_prime_distance_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x → ∀ t N : ℝ, 1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) →
        ‖zetaSum x t‖ = x / N →
        ∃ t₀ : ℝ, |t₀| ≤ Real.log x ∧
          (∀ u : ℝ, |u| ≤ Real.log x →
            ‖riemannZeta (twistZetaPoint x t u)‖ ≤ ‖riemannZeta (twistZetaPoint x t t₀)‖) ∧
          primePhaseDistance x (t - t₀) ≤
            (1 / 100 : ℝ) * Real.log (Real.log x) + Real.log (Real.log (Real.log x)) + C := by
  let D := ordinaryHalaszConstant
  let E := 4 * (Real.log 4 + 4) + 5
  let K := 2 * D * E
  have hD : 0 < D := ordinaryHalaszConstant_pos
  have hE : 0 < E := by dsimp [E]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨L₀, hL₀, herror⟩ := exists_ordinary_mean_error_threshold
  refine ⟨|Real.log K| + 1, by positivity, Real.exp L₀, ?_, ?_⟩
  · linarith [Real.add_one_le_exp L₀]
  intro x hx₀ t N hN hNtop hsum
  have hexp3 : 3 ≤ Real.exp L₀ := by linarith [Real.add_one_le_exp L₀]
  have hx : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hLlower : L₀ ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos L₀) hx₀
  have hxlog : 8 ≤ Real.log x := hL₀.trans hLlower
  have hN0 : 0 < N := by linarith
  let L := Real.log x
  have hL0 : 0 < L := Real.log_pos hx
  have hlogL : 0 < Real.log L := Real.log_pos (by change 1 < Real.log x; linarith)
  obtain ⟨t₀, ht₀, hmax, hmean⟩ := exists_maximizingTwist_prime_distance_mean_bound hx hxlog t
  refine ⟨t₀, ht₀, hmax, ?_⟩
  let M := primePhaseDistance x (t - t₀)
  have hM : 0 ≤ M := primePhaseDistance_nonneg _ _
  have hsum' : ‖zetaSum x t‖ / x = 1 / N := by rw [hsum]; field_simp
  rw [hsum'] at hmean
  have herr : D * ((1 + Real.log L) / L) ≤ 1 / (2 * N) := by
    apply (herror L hLlower).trans
    exact (div_le_div_iff₀ (by positivity : 0 < 2 * L ^ (1 / 100 : ℝ))
      (by positivity : 0 < 2 * N)).mpr (by nlinarith)
  have hhalf : 1 / (2 * N) ≤ D * ((M + 1) * Real.exp (-M)) := by
    have hid : 1 / N = 2 * (1 / (2 * N)) := by ring
    change 1 / N ≤ D * ((M + 1) * Real.exp (-M) + (1 + Real.log L) / L) at hmean
    rw [hid, mul_add] at hmean
    linarith
  have hexp : Real.exp M ≤ 2 * D * N * (M + 1) := by
    have hh := (div_le_iff₀ (show 0 < 2 * N by positivity)).mp hhalf
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos M).le
    have heq : Real.exp M * (D * ((M + 1) * Real.exp (-M)) * (2 * N)) =
        2 * D * N * (M + 1) := by
      rw [Real.exp_neg]
      field_simp
    simpa only [mul_one, heq] using hm
  have hcrude : M + 1 ≤ E * Real.log L := primePhaseDistance_add_one_le_log x (t - t₀) hx hxlog
  have hexp' : Real.exp M ≤ K * N * Real.log L := by
    have hh := hexp.trans (mul_le_mul_of_nonneg_left hcrude (show 0 ≤ 2 * D * N by positivity))
    convert hh using 1
    dsimp [K]
    ring
  have hlog := Real.log_le_log (Real.exp_pos M) hexp'
  rw [Real.log_exp, Real.log_mul (mul_pos hK hN0).ne' hlogL.ne', Real.log_mul hK.ne' hN0.ne'] at hlog
  have hlogN := Real.log_le_log hN0 hNtop
  rw [Real.log_rpow hL0] at hlogN
  have hKabs := le_abs_self (Real.log K)
  change M ≤ (1 / 100 : ℝ) * Real.log L + Real.log (Real.log L) + (|Real.log K| + 1)
  linarith

end
end DongWangWangZhang2026
