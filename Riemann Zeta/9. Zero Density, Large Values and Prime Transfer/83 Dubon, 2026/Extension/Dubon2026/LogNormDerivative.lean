import Dubon2026.HorizontalArgumentBound
import Dubon2026.LogTruncation
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! # Differentiation of the actual logarithmic norm away from its zeros -/

namespace Dubon2026

open Complex Filter MeasureTheory Set
open scoped Topology

theorem hasDerivAt_log_norm_complex {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hn : f x ≠ 0) :
    HasDerivAt (fun y => Real.log ‖f y‖) (f' / f x).re x := by
  have hr : HasDerivAt (fun y => (f y).re) f'.re x := reCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hi : HasDerivAt (fun y => (f y).im) f'.im x := imCLM.hasFDerivAt.comp_hasDerivAt x hf
  have hd : HasDerivAt (fun y => normSq (f y))
      (2 * ((f x).re * f'.re + (f x).im * f'.im)) x := by
    convert (hr.mul hr).add (hi.mul hi) using 1
    ring
  have hh := (hd.log (mt normSq_eq_zero.mp hn)).div_const 2
  convert hh using 1
  · ext y
    rw [normSq_eq_norm_sq, Real.log_pow]
    ring
  · rw [div_re]
    ring

theorem hasDerivAt_horizontal_logNorm (a : ℕ → ℂ) (N : ℕ) (σ t : ℝ)
    (hn : dirichletSum a N ((σ : ℂ) + I * t) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖dirichletSum a N ((x : ℂ) + I * t)‖)
      (logDeriv (dirichletSum a N) ((σ : ℂ) + I * t)).re σ :=
  hasDerivAt_log_norm_complex (hasDerivAt_horizontal_dirichletSum a N t σ) hn

theorem eventually_ne_zero_vertical_segment (a : ℕ → ℂ) (N : ℕ) (σ b t : ℝ)
    (hn : ∀ y ∈ Icc b t, dirichletSum a N ((σ : ℂ) + I * y) ≠ 0) :
    ∀ᶠ x : ℝ in 𝓝 σ, ∀ y ∈ Icc b t, dirichletSum a N ((x : ℂ) + I * y) ≠ 0 := by
  refine (isCompact_Icc : IsCompact (Icc b t)).eventually_forall_of_forall_eventually
    (P := fun x y : ℝ => dirichletSum a N ((x : ℂ) + I * y) ≠ 0) ?_
  intro y hy
  have hf : Continuous (dirichletSum a N) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).continuousAt
  have hc : Continuous (fun z : ℝ × ℝ => dirichletSum a N ((z.1 : ℂ) + I * z.2)) :=
    hf.comp (by fun_prop)
  exact (hc.continuousAt (x := (σ, y))).eventually_ne (hn y hy)

theorem continuousOn_vertical_logDeriv (a : ℕ → ℂ) (N : ℕ) (σ b t : ℝ)
    (hn : ∀ y ∈ Icc b t, dirichletSum a N ((σ : ℂ) + I * y) ≠ 0) :
    ContinuousOn (fun y : ℝ => logDeriv (dirichletSum a N) ((σ : ℂ) + I * y)) (Icc b t) := by
  have hf : Continuous (dirichletSum a N) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).continuousAt
  have hd : Continuous (deriv (dirichletSum a N)) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).deriv.continuousAt
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + I * y) := by fun_prop
  exact (hd.comp hc).continuousOn.div (hf.comp hc).continuousOn hn

end Dubon2026
