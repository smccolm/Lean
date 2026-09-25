import TaoTrudgianYang2025.SargosFourthGeometry

/-! Literal polynomial coordinates of Robert--Sargos (2002), (3.2) and
(4.15). The lower-degree Taylor terms are retained and bounded before
passing to the simpler counting system. No counting theorem is assumed. -/

noncomputable section
namespace TaoTrudgianYang2025

def robertSargosLinear (r q h n : ℝ) : ℝ := r*n+h*q

def robertSargosQuadratic (r q h n : ℝ) : ℝ :=
  r*n^2+2*h*q*n+h*q^2

def robertSargosReduced (r q₁ q₂ h₁ h₂ d : ℝ) : ℝ :=
  r*d^2+2*h₁*q₁*d+h₁*q₁^2-h₂*q₂^2

def robertSargosTaylorQuadratic (r q h n : ℝ) : ℝ :=
  h*q^2+2*h*q*n-r*n^2-r*h^2-r^2*h

theorem robertSargosLinear_shift (r q h n t : ℝ) :
    robertSargosLinear r q h (n+t) = robertSargosLinear r q h n+r*t := by
  unfold robertSargosLinear
  ring

theorem robertSargosQuadratic_shift (r q h n t : ℝ) :
    robertSargosQuadratic r q h (n+t) =
      robertSargosQuadratic r q h n+2*t*robertSargosLinear r q h n+r*t^2 := by
  unfold robertSargosQuadratic robertSargosLinear
  ring

theorem robertSargos_reduced_linear {r q₁ q₂ h₁ h₂ n₁ n₂ : ℝ}
    (h : robertSargosLinear r q₁ h₁ n₁ = robertSargosLinear r q₂ h₂ n₂) :
    r*(n₁-n₂)+h₁*q₁-h₂*q₂ = 0 := by
  unfold robertSargosLinear at h
  linarith

theorem robertSargos_quadratic_difference {r q₁ q₂ h₁ h₂ n₁ n₂ : ℝ}
    (h : robertSargosLinear r q₁ h₁ n₁ = robertSargosLinear r q₂ h₂ n₂) :
    robertSargosQuadratic r q₁ h₁ n₁-robertSargosQuadratic r q₂ h₂ n₂ =
      robertSargosReduced r q₁ q₂ h₁ h₂ (n₁-n₂) := by
  have hl := robertSargos_reduced_linear h
  unfold robertSargosQuadratic robertSargosReduced
  nlinarith only [mul_eq_zero_of_left hl (2*n₂)]

theorem robertSargos_reduced_symmetric {r q₁ q₂ h₁ h₂ d : ℝ}
    (h : r*d+h₁*q₁-h₂*q₂ = 0) :
    robertSargosReduced r q₁ q₂ h₁ h₂ d =
      (h₁*q₁+h₂*q₂)*d+h₁*q₁^2-h₂*q₂^2 := by
  unfold robertSargosReduced
  nlinarith only [mul_eq_zero_of_left h d]

theorem robertSargos_reduced_factor {r q₁ q₂ h₁ h₂ d : ℝ}
    (h : r*d+h₁*q₁-h₂*q₂ = 0) :
    r*robertSargosReduced r q₁ q₂ h₁ h₂ d =
      h₂*(h₂-r)*q₂^2-h₁*(h₁-r)*q₁^2 := by
  unfold robertSargosReduced
  have he : r*d = h₂*q₂-h₁*q₁ := by linarith only [h]
  calc
    r*(r*d^2+2*h₁*q₁*d+h₁*q₁^2-h₂*q₂^2) =
        (r*d)^2+2*h₁*q₁*(r*d)+r*h₁*q₁^2-r*h₂*q₂^2 := by ring
    _ = _ := by rw [he]; ring

theorem robertSargosTaylorQuadratic_eq (r q h n : ℝ) :
    robertSargosTaylorQuadratic r q h n =
      robertSargosQuadratic (-r) q h n-r*h^2-r^2*h := by
  unfold robertSargosTaylorQuadratic robertSargosQuadratic
  ring

theorem robertSargos_taylor_remainder_le {R H r h : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H)
    (hr : |r| ≤ R) (hh : |h| ≤ 2*H) :
    |r*h^2+r^2*h| ≤ 6*R*H^2 := by
  have hr2 : r^2 ≤ R^2 := by
    have ht := sq_le_sq₀ (abs_nonneg r) hR |>.mpr hr
    simpa only [sq_abs] using ht
  have hh2 : h^2 ≤ (2*H)^2 := by
    have ht := sq_le_sq₀ (abs_nonneg h) (by positivity : 0 ≤ 2*H) |>.mpr hh
    simpa only [sq_abs] using ht
  have hR2 : R^2 ≤ R*H := by nlinarith [mul_nonneg hR (sub_nonneg.mpr hRH)]
  calc
    _ ≤ |r*h^2|+|r^2*h| := abs_add_le _ _
    _ = |r| * h^2+r^2*|h| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg h),abs_of_nonneg (sq_nonneg r)]
    _ ≤ R*(2*H)^2+R^2*(2*H) :=
      add_le_add (mul_le_mul hr hh2 (sq_nonneg h) hR)
        (mul_le_mul hr2 hh (abs_nonneg h) (sq_nonneg R))
    _ ≤ 6*R*H^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hR2 hH]

/-- The actual Taylor phase is reduced only after charging both omitted
terms to the tolerance, as required in the paper's Step 7. -/
theorem robertSargos_actual_to_counting_tolerance {R H r q₁ q₂ h₁ h₂ n₁ n₂ E : ℝ}
    (hR : 0 ≤ R) (hH : 0 ≤ H) (hRH : R ≤ H)
    (hr : |r| ≤ R) (hh₁ : |h₁| ≤ 2*H) (hh₂ : |h₂| ≤ 2*H)
    (hlin : robertSargosLinear (-r) q₁ h₁ n₁ =
      robertSargosLinear (-r) q₂ h₂ n₂)
    (hnear : |robertSargosTaylorQuadratic r q₁ h₁ n₁-
      robertSargosTaylorQuadratic r q₂ h₂ n₂| ≤ E) :
    |robertSargosReduced (-r) q₁ q₂ h₁ h₂ (n₁-n₂)| ≤ E+12*R*H^2 := by
  rw [← robertSargos_quadratic_difference hlin]
  have hrem₁ := robertSargos_taylor_remainder_le hR hH hRH hr hh₁
  have hrem₂ := robertSargos_taylor_remainder_le hR hH hRH hr hh₂
  calc
    _ = |(robertSargosTaylorQuadratic r q₁ h₁ n₁-
        robertSargosTaylorQuadratic r q₂ h₂ n₂)+(r*h₁^2+r^2*h₁)-
        (r*h₂^2+r^2*h₂)| := by
      congr 1
      simp only [robertSargosTaylorQuadratic_eq]
      ring
    _ ≤ |robertSargosTaylorQuadratic r q₁ h₁ n₁-
        robertSargosTaylorQuadratic r q₂ h₂ n₂|+
        |r*h₁^2+r^2*h₁|+|r*h₂^2+r^2*h₂| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

end TaoTrudgianYang2025
