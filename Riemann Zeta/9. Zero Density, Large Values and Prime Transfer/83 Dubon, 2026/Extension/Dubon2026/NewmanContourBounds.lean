import Dubon2026.NewmanIntegrandBounds

/-! # Explicit three-edge bounds for the actual Tauberian contours -/

namespace Dubon2026

open Complex Set MeasureTheory

noncomputable section

/-- A uniform bound on the right three edges gives the perimeter times the bound. -/
theorem norm_newmanRightContour_le {F : ℂ → ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hh : ∀ x ∈ Icc 0 R, ‖F ((x : ℂ) - R * I)‖ ≤ C ∧ ‖F ((x : ℂ) + R * I)‖ ≤ C)
    (hv : ∀ y ∈ Icc (-R) R, ‖F ((R : ℂ) + y * I)‖ ≤ C) :
    ‖newmanRightContour F R‖ ≤ 4 * R * C := by
  have hb : ‖HIntegral F 0 R (-R)‖ ≤ C * R := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => F ((x : ℂ) - R * I)) (a := 0) (b := R) (C := C)
      (fun x hx => (hh x (by rw [uIoc_of_le hR] at hx; exact ⟨hx.1.le, hx.2⟩)).1)
    simpa [HIntegral, sub_eq_add_neg, abs_of_nonneg hR] using he
  have ht : ‖HIntegral F 0 R R‖ ≤ C * R := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq (by simp [abs_of_nonneg hR])
    intro x hx
    rw [uIoc_of_le hR] at hx
    exact (hh x ⟨hx.1.le, hx.2⟩).2
  have hrr : -R ≤ R := by linarith
  have hvr : ‖VIntegral F R (-R) R‖ ≤ C * (2 * R) := by
    simp only [VIntegral, norm_smul, norm_I, one_mul]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq ?_
    · intro y hy
      rw [uIoc_of_le hrr] at hy
      exact hv y ⟨hy.1.le, hy.2⟩
    · rw [show R - -R = 2 * R by ring, abs_of_nonneg (by positivity)]
  unfold newmanRightContour
  exact ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)).trans (by linarith)

/-- The matching left three edges obey the same perimeter bound. -/
theorem norm_newmanLeftContour_le {F : ℂ → ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hh : ∀ x ∈ Icc (-R) 0, ‖F ((x : ℂ) - R * I)‖ ≤ C ∧ ‖F ((x : ℂ) + R * I)‖ ≤ C)
    (hv : ∀ y ∈ Icc (-R) R, ‖F ((-R : ℂ) + y * I)‖ ≤ C) :
    ‖newmanLeftContour F R R‖ ≤ 4 * R * C := by
  have hr0 : -R ≤ 0 := by linarith
  have hb : ‖HIntegral F (-R) 0 (-R)‖ ≤ C * R := by
    have he := intervalIntegral.norm_integral_le_of_norm_le_const (f := fun x : ℝ => F ((x : ℂ) - R * I))
      (a := -R) (b := 0) (C := C) (fun x hx => (hh x (by
        rw [uIoc_of_le hr0] at hx
        exact ⟨hx.1.le, hx.2⟩)).1)
    simpa [HIntegral, sub_eq_add_neg, abs_of_nonneg hR] using he
  have ht : ‖HIntegral F (-R) 0 R‖ ≤ C * R := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq (by simp [abs_of_nonneg hR])
    intro x hx
    rw [uIoc_of_le hr0] at hx
    exact (hh x ⟨hx.1.le, hx.2⟩).2
  have hrr : -R ≤ R := by linarith
  have hvr : ‖VIntegral F (-R) (-R) R‖ ≤ C * (2 * R) := by
    simp only [VIntegral, norm_smul, norm_I, one_mul]
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := C) ?_).trans_eq ?_
    · intro y hy
      rw [uIoc_of_le hrr] at hy
      simpa using hv y ⟨hy.1.le, hy.2⟩
    · rw [show R - -R = 2 * R by ring, abs_of_nonneg (by positivity)]
  unfold newmanLeftContour
  exact (norm_sub_le _ _).trans ((add_le_add (norm_sub_le _ _) le_rfl).trans (by linarith))

/-- A right-half-plane Laplace tail bound gives the explicit O(1/R) right contour estimate. -/
theorem newman_right_square_bound {G : ℂ → ℂ} {B T R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hG : ∀ z : ℂ, 0 < z.re → ‖G z‖ ≤ B * Real.exp (-z.re * T) / z.re) :
    ‖newmanRightContour (newmanContourIntegrand G T R) R‖ ≤ 12 * B / R := by
  have hh : ∀ x ∈ Icc 0 R,
      ‖newmanContourIntegrand G T R ((x : ℂ) - R * I)‖ ≤ 3 * B / R ^ 2 ∧
      ‖newmanContourIntegrand G T R ((x : ℂ) + R * I)‖ ≤ 3 * B / R ^ 2 := by
    intro x hx
    constructor
    · apply norm_newmanContourIntegrand_horizontal_le hB hR
      · simpa using norm_newmanKernel_lower_le hR x
      · intro hn
        have hx0 : 0 < x := lt_of_le_of_ne hx.1 (by simpa [eq_comm] using hn)
        simpa [abs_of_pos hx0] using hG ((x : ℂ) - R * I) (by simpa using hx0)
    · apply norm_newmanContourIntegrand_horizontal_le hB hR
      · simpa using norm_newmanKernel_upper_le hR x
      · intro hn
        have hx0 : 0 < x := lt_of_le_of_ne hx.1 (by simpa [eq_comm] using hn)
        simpa [abs_of_pos hx0] using hG ((x : ℂ) + R * I) (by simpa using hx0)
  have hv : ∀ y ∈ Icc (-R) R,
      ‖newmanContourIntegrand G T R ((R : ℂ) + y * I)‖ ≤ 3 * B / R ^ 2 := by
    intro y hy
    apply norm_newmanContourIntegrand_vertical_le hB hR
    · simp [abs_of_pos hR]
    · simpa using abs_le.mpr hy
    · simpa [abs_of_pos hR] using hG ((R : ℂ) + y * I) (by simpa using hR)
  exact (norm_newmanRightContour_le hR.le hh hv).trans_eq (by field_simp; ring)

/-- A left-half-plane truncated Laplace bound gives the matching O(1/R) contour estimate. -/
theorem newman_left_square_bound {G : ℂ → ℂ} {B T R : ℝ} (hB : 0 ≤ B) (hR : 0 < R)
    (hG : ∀ z : ℂ, z.re < 0 → ‖G z‖ ≤ B * Real.exp (-z.re * T) / (-z.re)) :
    ‖newmanLeftContour (newmanContourIntegrand G T R) R R‖ ≤ 12 * B / R := by
  have hh : ∀ x ∈ Icc (-R) 0,
      ‖newmanContourIntegrand G T R ((x : ℂ) - R * I)‖ ≤ 3 * B / R ^ 2 ∧
      ‖newmanContourIntegrand G T R ((x : ℂ) + R * I)‖ ≤ 3 * B / R ^ 2 := by
    intro x hx
    constructor
    · apply norm_newmanContourIntegrand_horizontal_le hB hR
      · simpa using norm_newmanKernel_lower_le hR x
      · intro hn
        have hx0 : x < 0 := lt_of_le_of_ne hx.2 (by simpa using hn)
        simpa [abs_of_neg hx0] using hG ((x : ℂ) - R * I) (by simpa using hx0)
    · apply norm_newmanContourIntegrand_horizontal_le hB hR
      · simpa using norm_newmanKernel_upper_le hR x
      · intro hn
        have hx0 : x < 0 := lt_of_le_of_ne hx.2 (by simpa using hn)
        simpa [abs_of_neg hx0] using hG ((x : ℂ) + R * I) (by simpa using hx0)
  have hv : ∀ y ∈ Icc (-R) R,
      ‖newmanContourIntegrand G T R ((-R : ℂ) + y * I)‖ ≤ 3 * B / R ^ 2 := by
    intro y hy
    apply norm_newmanContourIntegrand_vertical_le hB hR
    · simp [abs_of_pos hR]
    · simpa using abs_le.mpr hy
    · simpa [abs_of_pos hR] using hG ((-R : ℂ) + y * I) (by simp; linarith)
  exact (norm_newmanLeftContour_le hR.le hh hv).trans_eq (by field_simp; ring)

end
end Dubon2026
