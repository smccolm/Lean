import Dubon2026.RieszMellinInversion
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Absolute convergence of the actual inverse Riesz integrand -/

namespace Dubon2026

open Complex MeasureTheory Filter

noncomputable section

/-- The actual inverse Mellin integrand for the quadratic cutoff. -/
def rieszInverseKernel (σ x t : ℝ) : ℂ :=
  (x : ℂ) ^ (-((σ : ℂ) + t * I)) * rieszMellinSymbol (σ + t * I)

/-- On a vertical line, the power factor has exactly constant modulus. -/
theorem norm_rieszInverseKernel {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    ‖rieszInverseKernel σ x t‖ = x ^ (-σ) * ‖rieszMellinSymbol (σ + t * I)‖ := by
  rw [rieszInverseKernel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The genuine inverse Mellin integrand is absolutely integrable for each positive argument. -/
theorem integrable_rieszInverseKernel {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    Integrable (rieszInverseKernel σ x) := by
  have hc : Continuous (rieszInverseKernel σ x) := by
    unfold rieszInverseKernel
    apply Continuous.mul _ (continuous_rieszMellinSymbol_vertical hσ)
    exact (by fun_prop : Continuous (fun t : ℝ => -((σ : ℂ) + t * I))).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  refine ((verticalIntegrable_rieszMellinSymbol hσ).norm.const_mul (x ^ (-σ))).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  exact le_of_eq (norm_rieszInverseKernel hx σ t)

/-- The literal integral of the inverse kernel is the actual cutoff with its exact Fourier normalization. -/
theorem integral_rieszInverseKernel {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ, rieszInverseKernel σ x t) =
      rieszMellinCutoff x := by
  simpa only [mellinInv, rieszInverseKernel, smul_eq_mul] using mellinInv_rieszMellinSymbol hσ hx

/-- Multiplication by an actual Dirichlet-series term is exactly dilation of the inverse kernel. -/
theorem rieszInverseKernel_mul_term {x : ℝ} (hx : 0 < x) (σ t : ℝ)
    (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    rieszInverseKernel σ x t * LSeries.term a (σ + t * I) n =
      a n * rieszInverseKernel σ ((n : ℝ) * x) t := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.term_of_ne_zero hn]
  have he := Complex.mul_cpow_ofReal_nonneg hnpos.le hx.le (-((σ : ℂ) + t * I))
  simp only [Complex.ofReal_natCast] at he
  simp only [rieszInverseKernel, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [he]
  simp only [Complex.cpow_neg]
  ring

/-- The exact norm separates the vertical kernel from the absolutely summable coefficient weights. -/
theorem norm_rieszInverseKernel_mul_term (σ x t : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖rieszInverseKernel σ x t * LSeries.term a (σ + t * I) n‖ =
      ‖LSeries.term a σ n‖ * ‖rieszInverseKernel σ x t‖ := by
  rw [norm_mul]
  have he : ‖LSeries.term a (σ + t * I) n‖ = ‖LSeries.term a σ n‖ := by
    simp only [LSeries.norm_term_eq]
    simp
  rw [he, mul_comm]

end
end Dubon2026
