import Dubon2026.MixedSpectralEulerInequality
import Mathlib.Logic.Equiv.Fin.Basic

/-! # The mixed Euler inequality for a genuine tensor square of any finite dimension -/

namespace Dubon2026

noncomputable section

/-- Unit-bounded roots give strictly convergent Euler coordinates on a real ray inside the unit disk. -/
theorem norm_spectral_real_coordinate_lt_one {w : ℂ} (hw : ‖w‖ ≤ 1) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) : ‖w * (a : ℂ)‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
  exact lt_of_le_of_lt (by simpa using mul_le_mul_of_nonneg_right hw ha0) ha1

/-- The tensor-square roots are constructed explicitly, and their literal Euler factor satisfies
the mixed Rankin inequality with its original symmetric factor. -/
theorem finiteTensorEuler_mixed_rankin {d : ℕ} (u : Fin d → ℂ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hu : ∀ i, ‖u i‖ ≤ 1)
    (hreal : ∀ m : ℕ, (∑ i : Fin d, u i ^ m).im = 0)
    {z : ℂ} (hz : ‖z‖ = 1) :
    1 ≤ ‖(∏ i : Fin d × Fin d, (1 - (u i.1 * u i.2) * (a : ℂ)))⁻¹ *
      ((1 - (a : ℂ))⁻¹) ^ 2 * ((∏ i : Fin d, (1 - u i * ((a : ℂ) * z)))⁻¹) ^ 4 *
        ((1 - (a : ℂ) * z ^ 2)⁻¹) ^ 2‖ := by
  let e : Fin d × Fin d ≃ Fin (d * d) := finProdFinEquiv
  let v : Fin (d * d) → ℂ := fun i => u (e.symm i).1 * u (e.symm i).2
  have hv (i : Fin (d * d)) : ‖v i‖ ≤ 1 := by
    dsimp only [v]
    rw [norm_mul]
    exact mul_le_one₀ (hu _) (norm_nonneg _) (hu _)
  have htrace (m : ℕ) : (∑ i : Fin (d * d), v i ^ m) = (∑ i : Fin d, u i ^ m) ^ 2 := by
    change (∑ i : Fin (d * d), (u (e.symm i).1 * u (e.symm i).2) ^ m) = _
    rw [e.symm.sum_comp (fun i => (u i.1 * u i.2) ^ m)]
    simp only [Fintype.sum_prod_type, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  have hh := finiteSpectralEuler_mixed_rankin u v ha0 ha1
    (fun i => norm_spectral_real_coordinate_lt_one (hu i) ha0 ha1)
    (fun i => norm_spectral_real_coordinate_lt_one (hv i) ha0 ha1) hreal htrace hz
  have he : (∏ i : Fin (d * d), (1 - v i * (a : ℂ))) =
      ∏ i : Fin d × Fin d, (1 - (u i.1 * u i.2) * (a : ℂ)) :=
    e.symm.prod_comp (fun i => 1 - (u i.1 * u i.2) * (a : ℂ))
  rwa [he] at hh

end
end Dubon2026
