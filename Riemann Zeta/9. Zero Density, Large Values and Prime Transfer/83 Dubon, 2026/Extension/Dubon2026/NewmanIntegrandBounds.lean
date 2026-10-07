import Dubon2026.NewmanRectangle
import Dubon2026.NewmanLaplace

/-! # Cancellation of the actual Laplace exponentials on Tauberian contours -/

namespace Dubon2026

open Complex

noncomputable section

/-- The exponential in the contour kernel cancels the genuine Laplace tail majorant. -/
theorem norm_newmanContourIntegrand_cancel {G : ℂ → ℂ} {B T R : ℝ} {z : ℂ}
    (hG : ‖G z‖ ≤ B * Real.exp (-z.re * T) / |z.re|) :
    ‖newmanContourIntegrand G T R z‖ ≤ B / |z.re| * ‖newmanKernel R z‖ := by
  have he : Real.exp (-z.re * T) * Real.exp (T * z.re) = 1 := by
    rw [← Real.exp_add, show -z.re * T + T * z.re = 0 by ring, Real.exp_zero]
  calc
    _ = ‖G z‖ * Real.exp (T * z.re) * ‖newmanKernel R z‖ := by
      simp [newmanContourIntegrand, Complex.norm_exp]
    _ ≤ (B * Real.exp (-z.re * T) / |z.re|) * Real.exp (T * z.re) *
        ‖newmanKernel R z‖ := by gcongr
    _ = _ := by
      calc
        _ = B / |z.re| * (Real.exp (-z.re * T) * Real.exp (T * z.re)) * ‖newmanKernel R z‖ := by ring
        _ = _ := by rw [he, mul_one]

/-- The vanishing horizontal kernel absorbs the singular bound at the imaginary axis. -/
theorem norm_newmanContourIntegrand_horizontal_le {G : ℂ → ℂ} {B T R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) {z : ℂ}
    (hk : ‖newmanKernel R z‖ ≤ 3 * |z.re| / R ^ 2)
    (hG : z.re ≠ 0 → ‖G z‖ ≤ B * Real.exp (-z.re * T) / |z.re|) :
    ‖newmanContourIntegrand G T R z‖ ≤ 3 * B / R ^ 2 := by
  by_cases hz : z.re = 0
  · have hk0 : newmanKernel R z = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hz] using hk) (norm_nonneg _))
    simp only [newmanContourIntegrand, hk0, mul_zero, norm_zero]
    positivity
  · have ha : 0 < |z.re| := abs_pos.mpr hz
    calc
      _ ≤ B / |z.re| * ‖newmanKernel R z‖ := norm_newmanContourIntegrand_cancel (hG hz)
      _ ≤ B / |z.re| * (3 * |z.re| / R ^ 2) := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by field_simp

/-- The square's vertical edges have the same uniform integrand majorant. -/
theorem norm_newmanContourIntegrand_vertical_le {G : ℂ → ℂ} {B T R : ℝ}
    (hB : 0 ≤ B) (hR : 0 < R) {z : ℂ} (hre : |z.re| = R) (him : |z.im| ≤ R)
    (hG : ‖G z‖ ≤ B * Real.exp (-z.re * T) / |z.re|) :
    ‖newmanContourIntegrand G T R z‖ ≤ 3 * B / R ^ 2 := by
  calc
    _ ≤ B / |z.re| * ‖newmanKernel R z‖ := norm_newmanContourIntegrand_cancel hG
    _ ≤ B / |z.re| * (3 / R) := mul_le_mul_of_nonneg_left
      (norm_newmanKernel_vertical_le hR hre him) (by positivity)
    _ = _ := by rw [hre]; ring

/-- Exact subtraction commutes with the common contour multiplier. -/
theorem newmanContourIntegrand_sub (G H : ℂ → ℂ) (T R : ℝ) :
    newmanContourIntegrand (G - H) T R =
      newmanContourIntegrand G T R - newmanContourIntegrand H T R := by
  funext z
  simp only [newmanContourIntegrand, Pi.sub_apply]
  ring

end
end Dubon2026
