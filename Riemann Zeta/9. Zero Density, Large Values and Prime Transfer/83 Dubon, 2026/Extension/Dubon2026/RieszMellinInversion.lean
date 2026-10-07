import Dubon2026.RieszMellinKernel

/-! # Absolute vertical integrability and exact inversion of the Riesz cutoff -/

namespace Dubon2026

open Complex Set MeasureTheory Filter
open scoped Topology

noncomputable section

private theorem norm_vertical_ge_one {a : ℝ} (ha : 1 ≤ a) (t : ℝ) :
    ‖(1 : ℂ) + t * I‖ ≤ ‖(a : ℂ) + t * I‖ := by
  have h1 := Complex.sq_norm ((1 : ℂ) + t * I)
  have ha' := Complex.sq_norm ((a : ℂ) + t * I)
  simp [Complex.normSq_apply] at h1 ha'
  nlinarith [norm_nonneg ((1 : ℂ) + t * I), norm_nonneg ((a : ℂ) + t * I)]

private theorem vertical_ne_zero {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (a : ℂ) + t * I ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  simp at hh
  linarith

/-- The exact cubic Mellin symbol has an integrable uniform vertical majorant. -/
theorem norm_rieszMellinSymbol_le {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    ‖rieszMellinSymbol (σ + t * I)‖ ≤ (1 / σ) * (1 + t ^ 2)⁻¹ := by
  have h0 : σ ≤ ‖(σ : ℂ) + t * I‖ := by
    simpa using Complex.re_le_norm ((σ : ℂ) + t * I)
  have h1 := norm_vertical_ge_one (show 1 ≤ σ + 1 by linarith) t
  have h2 := norm_vertical_ge_one (show 1 ≤ σ + 2 by linarith) t
  have he1 : (σ : ℂ) + t * I + 1 = ((σ + 1 : ℝ) : ℂ) + t * I := by push_cast; ring
  have he2 : (σ : ℂ) + t * I + 2 = ((σ + 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  have hsq : ‖(1 : ℂ) + t * I‖ * ‖(1 : ℂ) + t * I‖ = 1 + t ^ 2 := by
    rw [Complex.norm_mul_self_eq_normSq]
    simp [Complex.normSq_apply, pow_two]
  have hprod : σ * (1 + t ^ 2) ≤
      ‖(σ : ℂ) + t * I‖ * (‖(σ : ℂ) + t * I + 1‖ * ‖(σ : ℂ) + t * I + 2‖) := by
    rw [he1, he2, ← hsq]
    exact mul_le_mul h0 (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  unfold rieszMellinSymbol
  rw [norm_div, norm_one, norm_mul, norm_mul, mul_assoc]
  calc
    _ ≤ 1 / (σ * (1 + t ^ 2)) := one_div_le_one_div_of_le (by positivity) hprod
    _ = (1 / σ) * (1 + t ^ 2)⁻¹ := by rw [one_div, mul_inv]; ring

/-- The literal Mellin symbol is continuous along every positive vertical line. -/
theorem continuous_rieszMellinSymbol_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun t : ℝ => rieszMellinSymbol (σ + t * I)) := by
  unfold rieszMellinSymbol
  apply Continuous.div continuous_const (by fun_prop)
  intro t
  apply mul_ne_zero
  · apply mul_ne_zero (vertical_ne_zero hσ t)
    convert vertical_ne_zero (show 0 < σ + 1 by linarith) t using 1
    push_cast
    ring
  · convert vertical_ne_zero (show 0 < σ + 2 by linarith) t using 1
    push_cast
    ring

/-- Absolute convergence of the actual inverse Mellin symbol on every positive line. -/
theorem verticalIntegrable_rieszMellinSymbol {σ : ℝ} (hσ : 0 < σ) :
    VerticalIntegrable rieszMellinSymbol σ := by
  exact (integrable_inv_one_add_sq.const_mul (1 / σ)).mono'
    (continuous_rieszMellinSymbol_vertical hσ).aestronglyMeasurable
    (Eventually.of_forall (norm_rieszMellinSymbol_le hσ))

/-- The cutoff is continuous at every positive argument, including its upper endpoint. -/
theorem continuousAt_rieszMellinCutoff {x : ℝ} (hx : 0 < x) :
    ContinuousAt rieszMellinCutoff x := by
  have hcont : Continuous (fun y : ℝ => (rieszSecondKernel (1 - y) : ℂ)) := by
    unfold rieszSecondKernel
    fun_prop
  apply hcont.continuousAt.congr
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact (rieszMellinCutoff_eq hy).symm

/-- Inverse Mellin integration recovers the actual positive quadratic cutoff. -/
theorem mellinInv_rieszMellinSymbol {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    mellinInv σ rieszMellinSymbol x = rieszMellinCutoff x := by
  have he : ∀ t : ℝ, mellin rieszMellinCutoff (σ + t * I) =
      rieszMellinSymbol (σ + t * I) := fun t =>
    (hasMellin_rieszMellinCutoff (by simpa using hσ)).2
  have hi : VerticalIntegrable (mellin rieszMellinCutoff) σ := by
    unfold VerticalIntegrable
    simp_rw [he]
    exact verticalIntegrable_rieszMellinSymbol hσ
  have hm := mellinInv_mellin_eq σ rieszMellinCutoff hx
    (hasMellin_rieszMellinCutoff (by simpa using hσ)).1 hi
    (continuousAt_rieszMellinCutoff hx)
  simpa only [mellinInv, he] using hm

end
end Dubon2026
