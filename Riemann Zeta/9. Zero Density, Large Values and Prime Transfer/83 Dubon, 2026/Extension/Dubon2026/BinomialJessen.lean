import Dubon2026.PeriodicMean
import Dubon2026.CirclePolynomialLog

/-! # The actual logarithmic mean in the source's two-term normalization example -/

namespace Dubon2026

open Filter MeasureTheory Polynomial
open scoped Topology

noncomputable section

/-- The precise exponential polynomial in the paper's normalization example. -/
def binomialDirichlet (κ : ℝ) (s : ℂ) : ℂ := 1 + Complex.exp (-(κ : ℂ) * s)

theorem tendsto_polynomial_circle_log_mean (p : Polynomial ℂ) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log ‖p.eval (circleMap 0 1 t)‖) atTop (𝓝 p.logMahlerMeasure) := by
  have hp : Function.Periodic (fun t => Real.log ‖p.eval (circleMap 0 1 t)‖)
      (2 * Real.pi) := (periodic_circleMap 0 1).comp (fun z => Real.log ‖p.eval z‖)
  have hm := tendsto_periodic_symmetric_mean (mul_pos (by norm_num) Real.pi_pos)
    hp p.intervalIntegrable_mahlerMeasure
  simpa only [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, div_eq_mul_inv,
    mul_comm] using hm

theorem binomialDirichlet_vertical_eq_circle (κ σ t : ℝ) :
    binomialDirichlet κ ((σ : ℂ) + Complex.I * t) =
      (C (Real.exp (-κ * σ) : ℂ) * X + C 1).eval (circleMap 0 1 (-κ * t)) := by
  have he : -(κ : ℂ) * ((σ : ℂ) + Complex.I * t) =
      ((-κ * σ : ℝ) : ℂ) + ((-κ * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [binomialDirichlet, he, Complex.exp_add, ← Complex.ofReal_exp,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    circleMap_zero, Complex.ofReal_one, one_mul]
  ring

theorem logMahlerMeasure_binomial (x : ℝ) :
    (C (Real.exp x : ℂ) * X + C 1).logMahlerMeasure = max 0 x := by
  have hx : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)
  rw [logMahlerMeasure_C_mul_X_add_C hx]
  simp only [norm_inv, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos x), Real.log_exp, Real.posLog_def, Real.log_inv]
  rcases le_total 0 x with h | h
  · rw [max_eq_left (by linarith : -x ≤ 0), max_eq_right h]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ -x), max_eq_left h]
    ring

theorem tendsto_binomial_vertical_log_mean {κ : ℝ} (hκ : 0 < κ) (σ : ℝ) :
    Tendsto (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
      Real.log ‖binomialDirichlet κ ((σ : ℂ) + Complex.I * t)‖) atTop
        (𝓝 (max 0 (-κ * σ))) := by
  simp_rw [binomialDirichlet_vertical_eq_circle]
  have hh := tendsto_real_symmetric_mean_comp_negative hκ
    (tendsto_polynomial_circle_log_mean (C (Real.exp (-κ * σ) : ℂ) * X + C 1))
  simpa only [logMahlerMeasure_binomial] using hh

/-- The normalization example's Jessen function is defined by its actual vertical limit. -/
def binomialJessen (κ σ : ℝ) : ℝ :=
  limUnder atTop (fun T : ℝ => (2 * T)⁻¹ * ∫ t in -T..T,
    Real.log ‖binomialDirichlet κ ((σ : ℂ) + Complex.I * t)‖)

theorem binomialJessen_eq {κ : ℝ} (hκ : 0 < κ) (σ : ℝ) :
    binomialJessen κ σ = max 0 (-κ * σ) :=
  (tendsto_binomial_vertical_log_mean hκ σ).limUnder_eq

end

end Dubon2026
