import Dubon2026.RadialRecurrenceUniqueness
import Mathlib.RingTheory.Polynomial.Chebyshev

/-! # The exact spherical radial polynomial, including coincident Satake roots -/

namespace Dubon2026

noncomputable section
open Polynomial

/-- The full Chebyshev numerator of the spherical coefficient at an integer radius. -/
def sphericalChebyshevNumerator (q z : ℂ) (n : ℤ) : ℂ :=
  q * (Chebyshev.S ℂ n).eval z - (Chebyshev.S ℂ (n - 2)).eval z

/-- The literal numerator has the exact radius-zero normalization. -/
theorem sphericalChebyshevNumerator_zero (q z : ℂ) : sphericalChebyshevNumerator q z 0 = q + 1 := by
  simp [sphericalChebyshevNumerator, Chebyshev.S_neg_two]

/-- The literal numerator has the exact radius-one value. -/
theorem sphericalChebyshevNumerator_one (q z : ℂ) : sphericalChebyshevNumerator q z 1 = q * z := by
  simp [sphericalChebyshevNumerator, Chebyshev.S_neg_one]

/-- The actual numerator satisfies the characteristic-root recurrence at every integer radius. -/
theorem sphericalChebyshevNumerator_recurrence (q z : ℂ) (n : ℤ) :
    sphericalChebyshevNumerator q z (n + 2) =
      z * sphericalChebyshevNumerator q z (n + 1) - sphericalChebyshevNumerator q z n := by
  have h1 := congrArg (fun p : Polynomial ℂ => p.eval z) (Chebyshev.S_add_two ℂ n)
  have h2 := congrArg (fun p : Polynomial ℂ => p.eval z) (Chebyshev.S_add_two ℂ (n - 2))
  simp only [eval_sub, eval_mul, eval_X] at h1 h2
  have he1 : n + 2 - 2 = n := by ring
  have he2 : n + 1 - 2 = n - 2 + 1 := by ring
  have he3 : n - 2 + 2 = n := by ring
  unfold sphericalChebyshevNumerator
  rw [he1, he2]
  rw [he3] at h2
  linear_combination q * h1 - h2

/-- The exact spherical radial expression, with the actual square-root and double-coset normalization visible. -/
def sphericalChebyshevCoefficient (q r z : ℂ) (n : ℕ) : ℂ :=
  (r ^ n)⁻¹ * sphericalChebyshevNumerator q z n / (q + 1)

/-- The spherical expression is normalized to one at the identity. -/
theorem sphericalChebyshevCoefficient_zero (q r z : ℂ) (hq : q + 1 ≠ 0) :
    sphericalChebyshevCoefficient q r z 0 = 1 := by
  simp only [sphericalChebyshevCoefficient, pow_zero, inv_one, Nat.cast_zero,
    sphericalChebyshevNumerator_zero, one_mul]
  exact div_self hq

/-- The spherical expression has the exact original Hecke boundary equation. -/
theorem sphericalChebyshevCoefficient_boundary (q r z : ℂ) (hr : r ≠ 0)
    (hs : r ^ 2 = q) (hq : q + 1 ≠ 0) :
    (r * z) * sphericalChebyshevCoefficient q r z 0 =
      (q + 1) * sphericalChebyshevCoefficient q r z 1 := by
  rw [sphericalChebyshevCoefficient_zero q r z hq]
  simp only [sphericalChebyshevCoefficient, pow_one, Nat.cast_one, sphericalChebyshevNumerator_one]
  rw [← hs] at hq ⊢
  field_simp [hr, hq]

/-- The spherical expression satisfies the exact radius recurrence whenever the genuine square-root identity holds. -/
theorem sphericalChebyshevCoefficient_recurrence (q r z : ℂ) (hr : r ≠ 0)
    (hs : r ^ 2 = q) (hq : q + 1 ≠ 0) (n : ℕ) :
    (r * z) * sphericalChebyshevCoefficient q r z (n + 1) =
      sphericalChebyshevCoefficient q r z n + q * sphericalChebyshevCoefficient q r z (n + 2) := by
  have ha := sphericalChebyshevNumerator_recurrence q z n
  simp only [sphericalChebyshevCoefficient, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [ha, pow_add, pow_add, pow_one]
  rw [← hs] at hq ⊢
  field_simp [hr, hq]
  ring

end
end Dubon2026
