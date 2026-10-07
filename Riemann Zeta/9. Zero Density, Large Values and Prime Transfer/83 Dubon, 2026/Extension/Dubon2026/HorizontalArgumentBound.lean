import Dubon2026.HorizontalRealZeros
import Dubon2026.FiniteCrossingArgument
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv

/-! # Uniform horizontal argument bounds for the actual finite Dirichlet polynomial -/

namespace Dubon2026

open MeasureTheory Set

theorem hasDerivAt_horizontal_dirichletSum (a : ℕ → ℂ) (N : ℕ) (t σ : ℝ) :
    HasDerivAt (fun x : ℝ => dirichletSum a N ((x : ℂ) + Complex.I * t))
      (deriv (dirichletSum a N) ((σ : ℂ) + Complex.I * t)) σ := by
  have hh := ((analyticAt_dirichletSum a N ((σ : ℂ) + Complex.I * t)).differentiableAt.hasDerivAt.comp
    (σ : ℂ) ((hasDerivAt_id (σ : ℂ)).add_const (Complex.I * (t : ℂ)))).comp_ofReal
  simpa only [id_eq, mul_one] using hh

theorem intervalIntegrable_horizontal_logDeriv (a : ℕ → ℂ) (N : ℕ) (t : ℝ)
    {l u : ℝ} (hlu : l ≤ u)
    (hn : ∀ σ ∈ Icc l u, dirichletSum a N ((σ : ℂ) + Complex.I * t) ≠ 0) :
    IntervalIntegrable (fun σ : ℝ => logDeriv (dirichletSum a N)
      ((σ : ℂ) + Complex.I * t)) volume l u := by
  have hf : Continuous (dirichletSum a N) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).continuousAt
  have hd : Continuous (deriv (dirichletSum a N)) :=
    continuous_iff_continuousAt.mpr fun z => (analyticAt_dirichletSum a N z).deriv.continuousAt
  have hc : Continuous (fun σ : ℝ => (σ : ℂ) + Complex.I * t) := by fun_prop
  have hh := (hd.comp hc).continuousOn.div (hf.comp hc).continuousOn hn
  exact hh.intervalIntegrable_of_Icc hlu

theorem abs_im_horizontal_logDeriv_integral_le {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 = 1) (t : ℝ) {l u : ℝ} (hlu : l ≤ u)
    (hn : ∀ σ ∈ Icc l u, dirichletSum a N ((σ : ℂ) + Complex.I * t) ≠ 0) :
    |(∫ σ in l..u, logDeriv (dirichletSum a N) ((σ : ℂ) + Complex.I * t)).im| ≤
      Real.pi * (2 : ℝ) ^ N := by
  obtain ⟨Z, hZ, hcard⟩ := horizontal_real_zero_finset hN ha t
  have hh := abs_im_integral_logDerivative_le_of_finite_crossings
    (fun σ : ℝ => dirichletSum a N ((σ : ℂ) + Complex.I * t))
    (fun σ : ℝ => deriv (dirichletSum a N) ((σ : ℂ) + Complex.I * t)) Z l u hlu
    (fun σ _ => hasDerivAt_horizontal_dirichletSum a N t σ) hn
    (intervalIntegrable_horizontal_logDeriv a N t hlu hn)
    (fun σ _ hz => (hZ σ).mpr hz)
  exact hh.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard.le) Real.pi_pos.le)

end Dubon2026
