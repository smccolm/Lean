import Dubon2026.LogNormDerivative
import Dubon2026.ContourSlopeControl

/-! # The derivative of the actual finite-height logarithmic mean -/

namespace Dubon2026

open Complex Filter MeasureTheory Set
open scoped Topology

theorem hasDerivAt_integral_vertical_logNorm (a : ℕ → ℂ) (N : ℕ) (σ b t : ℝ)
    (hbt : b ≤ t)
    (hn : ∀ y ∈ Icc b t, dirichletSum a N ((σ : ℂ) + I * y) ≠ 0) :
    HasDerivAt (fun x : ℝ => ∫ y in b..t, Real.log ‖dirichletSum a N ((x : ℂ) + I * y)‖)
      (∫ y in b..t, logDeriv (dirichletSum a N) ((σ : ℂ) + I * y)).re σ := by
  have hf : Continuous (dirichletSum a N) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).continuousAt
  have hd : Continuous (deriv (dirichletSum a N)) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).deriv.continuousAt
  have hc (x : ℝ) : Continuous (fun y : ℝ => (x : ℂ) + I * y) := by fun_prop
  have hj : Continuous (fun z : ℝ × ℝ => (z.1 : ℂ) + I * z.2) := by fun_prop
  have hi : IntervalIntegrable (fun y : ℝ => logDeriv (dirichletSum a N)
      ((σ : ℂ) + I * y)) volume b t :=
    (continuousOn_vertical_logDeriv a N σ b t hn).intervalIntegrable_of_Icc hbt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_vertical_logDeriv a N σ b t hn)
  have hbound : ∀ᶠ x : ℝ in 𝓝 σ, ∀ y ∈ Icc b t,
      ‖logDeriv (dirichletSum a N) ((x : ℂ) + I * y)‖ ≤ C + 1 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro y hy
    have hcont : ContinuousAt (fun z : ℝ × ℝ =>
        logDeriv (dirichletSum a N) ((z.1 : ℂ) + I * z.2)) (σ, y) :=
      (hd.comp hj).continuousAt.div (hf.comp hj).continuousAt (hn y hy)
    have hh := hcont.norm.eventually_lt_const (show
      ‖logDeriv (dirichletSum a N) ((σ : ℂ) + I * y)‖ < C + 1 by linarith [hC y hy])
    exact hh.mono fun _ h => h.le
  let S := {x : ℝ | ∀ y ∈ Icc b t,
    dirichletSum a N ((x : ℂ) + I * y) ≠ 0 ∧
      ‖logDeriv (dirichletSum a N) ((x : ℂ) + I * y)‖ ≤ C + 1}
  have hs : S ∈ 𝓝 σ := by
    filter_upwards [eventually_ne_zero_vertical_segment a N σ b t hn, hbound] with x hx hB
    exact fun y hy => ⟨hx y hy, hB y hy⟩
  have hmeas (x : ℝ) : AEStronglyMeasurable
      (fun y : ℝ => Real.log ‖dirichletSum a N ((x : ℂ) + I * y)‖)
        (volume.restrict (Set.uIoc b t)) :=
    (Real.measurable_log.comp (hf.comp (hc x)).norm.measurable).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable (fun y : ℝ =>
      (logDeriv (dirichletSum a N) ((σ : ℂ) + I * y)).re)
        (volume.restrict (Set.uIoc b t)) :=
    (Complex.measurable_re.comp ((hd.comp (hc σ)).measurable.div
      (hf.comp (hc σ)).measurable)).aestronglyMeasurable
  have hsub {y : ℝ} (hy : y ∈ Set.uIoc b t) : y ∈ Icc b t := by
    rw [uIoc_of_le hbt] at hy
    exact ⟨hy.1.le, hy.2⟩
  have hh := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x y : ℝ => Real.log ‖dirichletSum a N ((x : ℂ) + I * y)‖)
    (F' := fun x y : ℝ => (logDeriv (dirichletSum a N) ((x : ℂ) + I * y)).re)
    (bound := fun _ : ℝ => C + 1) hs (Filter.Eventually.of_forall hmeas)
    (intervalIntegrable_vertical_log a N σ b t) hdmeas
    (Filter.Eventually.of_forall fun y hy x hx => by
      rw [Real.norm_eq_abs]
      exact (abs_re_le_norm (logDeriv (dirichletSum a N) ((x : ℂ) + I * y))).trans
        (hx y (hsub hy)).2)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun y hy x hx =>
      hasDerivAt_horizontal_logNorm a N x y (hx y (hsub hy)).1)
  have hre : (∫ y in b..t, (logDeriv (dirichletSum a N) ((σ : ℂ) + I * y)).re) =
      (∫ y in b..t, logDeriv (dirichletSum a N) ((σ : ℂ) + I * y)).re :=
    intervalIntegral.intervalIntegral_re hi
  simpa only [hre] using hh.2

theorem hasDerivAt_verticalLogMean (a : ℕ → ℂ) (N : ℕ) (σ T : ℝ) (hT : 0 ≤ T)
    (hn : ∀ y ∈ Icc (-T) T, dirichletSum a N ((σ : ℂ) + I * y) ≠ 0) :
    HasDerivAt (fun x => verticalLogMean a N x T) (verticalLogDerivMean a N σ T) σ := by
  have hh := (hasDerivAt_integral_vertical_logNorm a N σ (-T) T (neg_le_self hT) hn).const_mul
    ((2 * T)⁻¹)
  convert hh using 1
  unfold verticalLogDerivMean
  ring

end Dubon2026
