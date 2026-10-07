import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! # Shifted Gaussian Poisson summation with its exact phase -/

namespace Dubon2026

open Complex

noncomputable section

/-- Completing the square in pinned Mathlib's Gaussian Poisson formula retains the exact phase and square-root factor. -/
theorem tsum_shifted_complex_gaussian {a : ℂ} (ha : 0 < a.re) (x : ℂ) :
    (∑' n : ℤ, Complex.exp (-(Real.pi : ℂ) * a * ((n : ℂ) + x) ^ 2)) =
      1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ,
        Complex.exp (-(Real.pi : ℂ) / a * (n : ℂ) ^ 2 + 2 * Real.pi * I * n * x) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp only [h, zero_re, lt_self_iff_false] at ha
  have hleft (n : ℤ) :
      -(Real.pi : ℂ) * a * ((n : ℂ) + x) ^ 2 =
        -(Real.pi : ℂ) * a * x ^ 2 +
          (-(Real.pi : ℂ) * a * (n : ℂ) ^ 2 + 2 * Real.pi * (-a * x) * n) := by ring
  have hright (n : ℤ) :
      -(Real.pi : ℂ) * a * x ^ 2 +
        (-(Real.pi : ℂ) / a * ((n : ℂ) + I * (-a * x)) ^ 2) =
          -(Real.pi : ℂ) / a * (n : ℂ) ^ 2 + 2 * Real.pi * I * n * x := by
    field_simp
    ring_nf
    simp only [I_sq]
    ring
  simp_rw [hleft, Complex.exp_add (-(Real.pi : ℂ) * a * x ^ 2)]
  rw [tsum_mul_left, Complex.tsum_exp_neg_quadratic ha, ← mul_assoc,
    mul_comm (Complex.exp _) (1 / a ^ (1 / 2 : ℂ)), mul_assoc, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [← Complex.exp_add, hright]

end
end Dubon2026
