import Dubon2026.RieszPerron

/-! # The literal vertical Perron integral and its absolute convergence -/

namespace Dubon2026

open Complex MeasureTheory

noncomputable section

/-- The dilated inverse kernel is exactly the conventional Perron power divided by the cubic symbol. -/
theorem rieszPerron_integrand_eq {x : ℝ} (hx : 0 < x) (σ t : ℝ) :
    (x : ℂ) ^ 2 * rieszInverseKernel σ x⁻¹ t =
      (x : ℂ) ^ ((σ : ℂ) + t * I + 2) /
        (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2)) := by
  have hxarg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos.ne
  rw [rieszInverseKernel, Complex.ofReal_inv, Complex.inv_cpow _ _ hxarg,
    Complex.cpow_neg, inv_inv, Complex.cpow_add ((σ : ℂ) + t * I) 2 (Complex.ofReal_ne_zero.mpr hx.ne')]
  norm_num only [Complex.cpow_ofNat]
  unfold rieszMellinSymbol
  ring

/-- The actual vertical Perron integrand is absolutely integrable wherever its coefficient series converges. -/
theorem integrable_rieszPerron {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    {a : ℕ → ℂ} (ha : LSeriesSummable a σ) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + t * I + 2) * LSeries a (σ + t * I) /
        (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2))) := by
  have hi := (integrable_rieszInverseKernel_LSeries hσ (inv_pos.mpr hx) ha).const_mul ((x : ℂ) ^ 2)
  convert hi using 1
  funext t
  rw [← mul_assoc, rieszPerron_integrand_eq hx]
  ring

/-- The literal positive-index quadratic sum equals its absolutely convergent vertical contour integral. -/
theorem rieszPerron_integral_formula {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    {a : ℕ → ℂ} (ha : LSeriesSummable a σ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n) ^ 2 / 2) =
      (1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + t * I + 2) * LSeries a (σ + t * I) /
          (((σ : ℂ) + t * I) * ((σ : ℂ) + t * I + 1) * ((σ : ℂ) + t * I + 2)) := by
  rw [← rieszPerron_formula hσ hx ha, mellinInv, mul_smul_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [smul_eq_mul]
  have he := rieszPerron_integrand_eq hx σ t
  unfold rieszInverseKernel at he
  calc
    _ = ((x : ℂ) ^ 2 * ((x⁻¹ : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) *
          rieszMellinSymbol (σ + t * I)) * LSeries a (σ + t * I) := by ring
    _ = _ := by rw [mul_assoc ((x : ℂ) ^ 2), he]; ring

end
end Dubon2026
