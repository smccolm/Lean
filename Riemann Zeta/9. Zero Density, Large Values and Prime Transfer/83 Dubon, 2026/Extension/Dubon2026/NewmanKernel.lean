import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! # Exact rectangular contour kernel bounds for analytic Tauberian inversion -/

namespace Dubon2026

noncomputable section

/-- The actual pole kernel, with zeros at the two horizontal contour endpoints. -/
def newmanKernel (R : ℝ) (z : ℂ) : ℂ := (1 + z ^ 2 / (R : ℂ) ^ 2) / z

/-- The kernel splits into its simple pole and its entire linear part. -/
theorem newmanKernel_eq (R : ℝ) (z : ℂ) :
    newmanKernel R z = 1 / z + z / (R : ℂ) ^ 2 := by
  by_cases hz : z = 0
  · simp [newmanKernel, hz]
  unfold newmanKernel
  rw [add_div, div_right_comm, show z ^ 2 / z = z by rw [pow_two, mul_div_cancel_right₀ z hz]]

/-- Exact factorization on the upper horizontal line displays cancellation at its imaginary endpoint. -/
theorem newmanKernel_horizontal_factor {R : ℝ} (hR : 0 < R) (x : ℝ) :
    newmanKernel R ((x : ℂ) + R * Complex.I) =
      ((x : ℂ) / (R : ℂ) ^ 2) *
        (((x : ℂ) + 2 * R * Complex.I) / ((x : ℂ) + R * Complex.I)) := by
  have hz : (x : ℂ) + R * Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.zero_im] at hi
    exact hR.ne' hi
  unfold newmanKernel
  field_simp [Complex.ofReal_ne_zero.mpr hR.ne', hz]
  ring_nf
  simp [Complex.I_sq]

/-- On either horizontal line the kernel is bounded by a constant times distance from the imaginary axis. -/
theorem norm_newmanKernel_upper_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖newmanKernel R ((x : ℂ) + R * Complex.I)‖ ≤ 3 * |x| / R ^ 2 := by
  let z : ℂ := (x : ℂ) + R * Complex.I
  have hre : |x| ≤ ‖z‖ := by simpa [z] using Complex.abs_re_le_norm z
  have him : R ≤ ‖z‖ := by simpa [z, abs_of_pos hR] using Complex.abs_im_le_norm z
  have hz : 0 < ‖z‖ := hR.trans_le him
  have hb : ‖(x : ℂ) + 2 * R * Complex.I‖ ≤ 3 * ‖z‖ := by
    have hh := norm_add_le (x : ℂ) (2 * R * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos hR] at hh
    norm_num at hh
    linarith
  rw [newmanKernel_horizontal_factor hR x]
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hr : ‖(x : ℂ) + 2 * R * Complex.I‖ / ‖z‖ ≤ 3 := (div_le_iff₀ hz).mpr hb
  calc
    _ ≤ (|x| / R ^ 2) * 3 := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

/-- The real-parameter kernel respects complex conjugation. -/
theorem newmanKernel_conj (R : ℝ) (z : ℂ) :
    newmanKernel R (starRingEnd ℂ z) = starRingEnd ℂ (newmanKernel R z) := by
  simp [newmanKernel]

/-- The matching lower horizontal edge has the same exact bound. -/
theorem norm_newmanKernel_lower_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖newmanKernel R ((x : ℂ) - R * Complex.I)‖ ≤ 3 * |x| / R ^ 2 := by
  have he : (x : ℂ) - R * Complex.I = starRingEnd ℂ ((x : ℂ) + R * Complex.I) := by simp [sub_eq_add_neg]
  rw [he, newmanKernel_conj, RCLike.norm_conj]
  exact norm_newmanKernel_upper_le hR x

/-- On the two vertical edges of the square contour the kernel is uniformly O(1/R). -/
theorem norm_newmanKernel_vertical_le {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hre : |z.re| = R) (him : |z.im| ≤ R) :
    ‖newmanKernel R z‖ ≤ 3 / R := by
  have hlow : R ≤ ‖z‖ := hre ▸ Complex.abs_re_le_norm z
  have hhigh : ‖z‖ ≤ 2 * R := (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [hre]; linarith)
  rw [newmanKernel_eq]
  apply (norm_add_le _ _).trans
  simp only [norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hi : 1 / ‖z‖ ≤ 1 / R := one_div_le_one_div_of_le hR hlow
  have hh : ‖z‖ / R ^ 2 ≤ (2 * R) / R ^ 2 := div_le_div_of_nonneg_right hhigh (sq_nonneg _)
  have he : 1 / R + (2 * R) / R ^ 2 = 3 / R := by field_simp; ring
  exact (add_le_add hi hh).trans_eq he

end
end Dubon2026
