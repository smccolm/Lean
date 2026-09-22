import GafniTao.FordLeftLine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convolution

/-!
# Absolute convergence on Ford's shifted left edge

This file proves integrability of the literal envelope produced by
`norm_fordLeftLine_logDeriv_mul_le`.  The proof retains Ford's translated
quadratic denominator and logarithmic numerator.  Its global majorant is the
integrable Japanese-bracket power `(1 + u²)⁻³⁄⁴`.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

/-- A uniform fractional-power majorant for the logarithm occurring on
Ford's left edge. -/
theorem ford_log_abs_add_two_le_japaneseQuarter (u : ℝ) :
    Real.log (|u| + 2) ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by
  let q : ℝ := 1 + u ^ 2
  have hq : 0 < q := by positivity
  have hx : 0 ≤ |u| + 2 := by positivity
  have hlog := Real.log_le_rpow_div hx (show (0 : ℝ) < 1 / 2 by norm_num)
  have habs : |u| ≤ Real.sqrt q := by
    rw [← Real.sqrt_sq_eq_abs u]
    exact Real.sqrt_le_sqrt (by dsimp [q]; linarith)
  have hsqrt1 : 1 ≤ Real.sqrt q := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by dsimp [q]; nlinarith [sq_nonneg u])
  have hxq : |u| + 2 ≤ 4 * Real.sqrt q := by nlinarith
  have hrpow := Real.rpow_le_rpow hx hxq (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [Real.sqrt_eq_rpow] at hrpow
  have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by norm_num
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
      (Real.rpow_nonneg hq.le _),
    hfour, ← Real.rpow_mul hq.le] at hrpow
  norm_num at hrpow
  dsimp [q] at hrpow
  exact hlog.trans (by nlinarith)

/-- The logarithmic standard quadratic envelope is integrable. -/
theorem integrable_ford_log_standard_envelope :
    Integrable (fun u : ℝ => Real.log (|u| + 2) / (1 + u ^ 2)) := by
  have hraw : Integrable (fun u : ℝ =>
      (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    integrable_rpow_neg_one_add_norm_sq (by norm_num)
  have hbase : Integrable (fun u : ℝ =>
      4 * (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) := hraw.const_mul 4
  apply hbase.mono'
  · have hnum : Continuous (fun u : ℝ => Real.log (|u| + 2)) := by
      apply Continuous.log
      · fun_prop
      · intro u
        positivity
    have hden : Continuous (fun u : ℝ => 1 + u ^ 2) := by fun_prop
    exact (hnum.div hden (by intro u; positivity)).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs]
  have hlogNonneg : 0 ≤ Real.log (|u| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg u])
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlogNonneg (by positivity))]
  have hlog := ford_log_abs_add_two_le_japaneseQuarter u
  have hq : 0 < 1 + u ^ 2 := by positivity
  let q : ℝ := 1 + u ^ 2
  have hid : q ^ (-(3 / 4 : ℝ)) * q = q ^ (1 / 4 : ℝ) := by
    calc
      q ^ (-(3 / 4 : ℝ)) * q =
          q ^ (-(3 / 4 : ℝ)) * q ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = q ^ (-(3 / 4 : ℝ) + 1) := (Real.rpow_add hq _ _).symm
      _ = q ^ (1 / 4 : ℝ) := by norm_num
  rw [div_le_iff₀ hq]
  rw [show (-(3 / 2 : ℝ) / 2) = -(3 / 4 : ℝ) by norm_num]
  calc
    Real.log (|u| + 2) ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := hlog
    _ = (4 * (1 + u ^ 2) ^ (-(3 / 4 : ℝ))) * (1 + u ^ 2) := by
      dsimp [q] at hid
      rw [mul_assoc, hid]
    _ = (4 * (1 + |u| ^ 2) ^ (-(3 / 4 : ℝ))) * (1 + u ^ 2) := by
      rw [sq_abs]

/-- Every positive-width quadratic Cauchy envelope is integrable. -/
theorem integrable_ford_inv_quadratic (a : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => 1 / (a ^ 2 + u ^ 2)) := by
  let c : ℝ := min (a ^ 2) 1
  have hc : 0 < c := lt_min (sq_pos_of_pos ha) zero_lt_one
  have hbase : Integrable (fun u : ℝ =>
      (1 / c) * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (1 / c)
  apply hbase.mono'
  · have hden : Continuous (fun u : ℝ => a ^ 2 + u ^ 2) := by fun_prop
    exact (continuous_const.div hden (by intro u; positivity)).aestronglyMeasurable
  filter_upwards [] with u
  have hden : 0 < a ^ 2 + u ^ 2 := by positivity
  have hq : 0 < 1 + u ^ 2 := by positivity
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcomp : c * (1 + u ^ 2) ≤ a ^ 2 + u ^ 2 := by
    nlinarith [min_le_left (a ^ 2) 1,
      mul_le_mul_of_nonneg_right hc1 (sq_nonneg u)]
  simp only [Real.norm_eq_abs, abs_of_pos (div_pos zero_lt_one hden)]
  calc
    1 / (a ^ 2 + u ^ 2) ≤ 1 / (c * (1 + u ^ 2)) :=
      one_div_le_one_div_of_le (mul_pos hc hq) hcomp
    _ = (1 / c) * (1 + u ^ 2)⁻¹ := by field_simp

/-- The unshifted logarithmic envelope remains integrable for every positive
horizontal distance from the left contour. -/
theorem integrable_ford_log_quadratic (a : ℝ) (ha : 0 < a) :
    Integrable (fun u : ℝ => Real.log (|u| + 2) / (a ^ 2 + u ^ 2)) := by
  let c : ℝ := min (a ^ 2) 1
  have hc : 0 < c := lt_min (sq_pos_of_pos ha) zero_lt_one
  have hbase : Integrable (fun u : ℝ =>
      (1 / c) * (Real.log (|u| + 2) / (1 + u ^ 2))) :=
    integrable_ford_log_standard_envelope.const_mul (1 / c)
  apply hbase.mono'
  · have hnum : Continuous (fun u : ℝ => Real.log (|u| + 2)) := by
      apply Continuous.log
      · fun_prop
      · intro u; positivity
    have hden : Continuous (fun u : ℝ => a ^ 2 + u ^ 2) := by fun_prop
    exact (hnum.div hden (by intro u; positivity)).aestronglyMeasurable
  filter_upwards [] with u
  have hden : 0 < a ^ 2 + u ^ 2 := by positivity
  have hq : 0 < 1 + u ^ 2 := by positivity
  have hlog : 0 ≤ Real.log (|u| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg u])
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcomp : c * (1 + u ^ 2) ≤ a ^ 2 + u ^ 2 := by
    nlinarith [min_le_left (a ^ 2) 1,
      mul_le_mul_of_nonneg_right hc1 (sq_nonneg u)]
  simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlog hden.le)]
  calc
    Real.log (|u| + 2) / (a ^ 2 + u ^ 2) ≤
        Real.log (|u| + 2) / (c * (1 + u ^ 2)) :=
      div_le_div_of_nonneg_left hlog (mul_pos hc hq) hcomp
    _ = (1 / c) * (Real.log (|u| + 2) / (1 + u ^ 2)) := by field_simp

/-- Ford's literal translated left-edge envelope is integrable. -/
theorem integrable_ford_leftLine_envelope
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    Integrable (fun u : ℝ =>
      Real.log (|u| + 2) /
        ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2)) := by
  let a : ℝ := sigma + 1 / 2
  have ha : 0 < a := by dsimp [a]; linarith
  let f : ℝ → ℝ := fun v =>
    Real.log (|t - v| + 2) / (a ^ 2 + v ^ 2)
  have hlogt : 0 ≤ Real.log (|t| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg t])
  have hmajor : Integrable (fun v : ℝ =>
      Real.log (|v| + 2) / (a ^ 2 + v ^ 2) +
        Real.log (|t| + 2) * (1 / (a ^ 2 + v ^ 2))) :=
    (integrable_ford_log_quadratic a ha).add
      ((integrable_ford_inv_quadratic a ha).const_mul (Real.log (|t| + 2)))
  have hf : Integrable f := by
    apply hmajor.mono'
    · dsimp [f]
      have hnum : Continuous (fun v : ℝ => Real.log (|t - v| + 2)) := by
        apply Continuous.log
        · fun_prop
        · intro v; positivity
      have hden : Continuous (fun v : ℝ => a ^ 2 + v ^ 2) := by fun_prop
      exact (hnum.div hden (by intro v; positivity)).aestronglyMeasurable
    filter_upwards [] with v
    have hden : 0 < a ^ 2 + v ^ 2 := by positivity
    have hvpos : 0 < |v| + 2 := by positivity
    have htpos : 0 < |t| + 2 := by positivity
    have htvpos : 0 < |t - v| + 2 := by positivity
    have hprod : |t - v| + 2 ≤ (|v| + 2) * (|t| + 2) := by
      rw [abs_sub_comm]
      calc
        |v - t| + 2 ≤ (|v| + |t|) + 2 := by
          linarith [abs_sub v t]
        _ ≤ (|v| + 2) * (|t| + 2) := by
          nlinarith [abs_nonneg v, abs_nonneg t]
    have hlogle : Real.log (|t - v| + 2) ≤
        Real.log (|v| + 2) + Real.log (|t| + 2) := by
      calc
        Real.log (|t - v| + 2) ≤ Real.log ((|v| + 2) * (|t| + 2)) :=
          Real.log_le_log htvpos hprod
        _ = _ := Real.log_mul hvpos.ne' htpos.ne'
    have hnumNonneg : 0 ≤ Real.log (|t - v| + 2) :=
      Real.log_nonneg (by linarith [abs_nonneg (t - v)])
    dsimp [f]
    simp only [abs_of_nonneg (div_nonneg hnumNonneg hden.le)]
    calc
      Real.log (|t - v| + 2) / (a ^ 2 + v ^ 2) ≤
          (Real.log (|v| + 2) + Real.log (|t| + 2)) /
            (a ^ 2 + v ^ 2) := div_le_div_of_nonneg_right hlogle hden.le
      _ = Real.log (|v| + 2) / (a ^ 2 + v ^ 2) +
          Real.log (|t| + 2) * (1 / (a ^ 2 + v ^ 2)) := by ring
  have hcomp := (MeasureTheory.integrable_comp_sub_left f t).2 hf
  simpa [f, a] using hcomp

/-- Absolute convergence of Ford's left-edge logarithmic-derivative
integrand from the source Laplace-remainder bound.  Measurability is kept as
an explicit analytic side condition here; the later Laplace-transform
specialization derives it from the transform's holomorphy. -/
theorem integrable_fordLeftLine_logDeriv_mul_of_aestronglyMeasurable
    {F₀ : ℂ → ℂ} {sigma t D eta C : ℝ}
    (hsigma : 1 < sigma) (hetaUpper : eta ≤ 3 / 2)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → eta ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2)
    (hlogDeriv : ∀ u : ℝ,
      ‖deriv riemannZeta (fordLeftLinePoint u) /
        riemannZeta (fordLeftLinePoint u)‖ ≤
          C * Real.log (|u| + 2))
    (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable (fun u : ℝ =>
      (-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (((sigma : ℂ) + (t : ℂ) * Complex.I) - fordLeftLinePoint u))) :
    Integrable (fun u : ℝ =>
      (-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (((sigma : ℂ) + (t : ℂ) * Complex.I) - fordLeftLinePoint u)) := by
  have henv := integrable_ford_leftLine_envelope
    (sigma := sigma) (t := t) hsigma
  have hmajor : Integrable (fun u : ℝ =>
      (C * D) * (Real.log (|u| + 2) /
        ((sigma + 1 / 2) ^ 2 + (t - u) ^ 2))) :=
    henv.const_mul (C * D)
  apply hmajor.mono' hmeas
  filter_upwards [] with u
  have hpoint := norm_fordLeftLine_logDeriv_mul_le
    (F₀ := F₀) (sigma := sigma) (t := t) (D := D) (eta := eta) (C := C)
    hsigma hetaUpper hF₀ hlogDeriv hC u
  simpa [mul_div_assoc, mul_assoc] using hpoint

/-- Continuity of the exact left-line integrand.  In particular, the
measurability side condition in the envelope lemma is derived rather than
assumed in Ford's contour application. -/
theorem continuous_fordLeftLine_logDeriv_mul
    {F₀ : ℂ → ℂ} {s : ℂ}
    (hs : 1 < s.re)
    (hFdiff : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) :
    Continuous (fun u : ℝ =>
      (-deriv riemannZeta (fordLeftLinePoint u) /
          riemannZeta (fordLeftLinePoint u)) *
        F₀ (s - fordLeftLinePoint u)) := by
  have hp : Continuous fordLeftLinePoint := by
    unfold fordLeftLinePoint
    fun_prop
  have hpOne : ∀ u : ℝ, fordLeftLinePoint u ≠ 1 := by
    intro u h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hz : Continuous (fun u : ℝ => riemannZeta (fordLeftLinePoint u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (analyticAt_riemannZeta (hpOne u)).continuousAt.comp_of_eq
      hp.continuousAt rfl
  have hdz : Continuous
      (fun u : ℝ => deriv riemannZeta (fordLeftLinePoint u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact (differentiableAt_deriv_riemannZeta (hpOne u)).continuousAt.comp_of_eq
      hp.continuousAt rfl
  have hF : Continuous (fun u : ℝ => F₀ (s - fordLeftLinePoint u)) := by
    rw [continuous_iff_continuousAt]
    intro u
    have hre : 0 < (s - fordLeftLinePoint u).re := by
      simp
      linarith
    exact (hFdiff _ hre).continuousAt.comp_of_eq
      (continuousAt_const.sub hp.continuousAt) rfl
  exact (hdz.neg.div hz (fun u => ford_leftLine_zeta_ne_zero u)).mul hF


end

end GafniTao
