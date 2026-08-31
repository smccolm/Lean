import GafniTao.FordSource

/-!
# Ford's trigonometric polynomial

This file formalizes the exact nonnegative trigonometric polynomial used in
Section 5 of Ford's zero-free-region argument.  The coefficients and the
factorization are those displayed immediately before Ford's Lemma 5.1.
-/

namespace GafniTao

def fordTrigB4 : ℝ := 1

def fordTrigB3 (a₁ a₂ : ℝ) : ℝ := 4 * (a₁ + a₂)

def fordTrigB2 (a₁ a₂ : ℝ) : ℝ :=
  4 * (1 + a₁ ^ 2 + a₂ ^ 2 + 4 * a₁ * a₂)

def fordTrigB1 (a₁ a₂ : ℝ) : ℝ :=
  (a₁ + a₂) * (12 + 16 * a₁ * a₂)

def fordTrigB0 (a₁ a₂ : ℝ) : ℝ :=
  fordTrigB2 a₁ a₂ - 1 + 8 * (a₁ * a₂) ^ 2

/-- The literal five-frequency left side of Ford's trigonometric identity. -/
noncomputable def fordTrigSum (a₁ a₂ θ : ℝ) : ℝ :=
  fordTrigB0 a₁ a₂ +
    fordTrigB1 a₁ a₂ * Real.cos θ +
    fordTrigB2 a₁ a₂ * Real.cos (2 * θ) +
    fordTrigB3 a₁ a₂ * Real.cos (3 * θ) +
    fordTrigB4 * Real.cos (4 * θ)

theorem ford_cos_four_mul (x : ℝ) :
    Real.cos (4 * x) = 8 * Real.cos x ^ 4 - 8 * Real.cos x ^ 2 + 1 := by
  rw [show (4 : ℝ) * x = 2 * (2 * x) by ring, Real.cos_two_mul,
    Real.cos_two_mul]
  ring

/-- Ford's exact Section 5 factorization. -/
theorem ford_trigonometric_identity (a₁ a₂ θ : ℝ) :
    fordTrigSum a₁ a₂ θ =
      8 * (Real.cos θ + a₁) ^ 2 * (Real.cos θ + a₂) ^ 2 := by
  rw [fordTrigSum, Real.cos_two_mul, Real.cos_three_mul, ford_cos_four_mul]
  simp only [fordTrigB0, fordTrigB1, fordTrigB2, fordTrigB3, fordTrigB4]
  ring

/-- The polynomial is nonnegative for all real parameters, exactly as needed
when Ford applies the Euler product frequency by frequency. -/
theorem ford_trigonometric_nonneg (a₁ a₂ θ : ℝ) :
    0 ≤ fordTrigSum a₁ a₂ θ := by
  rw [ford_trigonometric_identity]
  positivity

/-- The nonconstant part which occurs after expanding `log |ζ|` by its
Euler product. -/
noncomputable def fordTrigOscillatory (a₁ a₂ θ : ℝ) : ℝ :=
  fordTrigB1 a₁ a₂ * Real.cos θ +
    fordTrigB2 a₁ a₂ * Real.cos (2 * θ) +
    fordTrigB3 a₁ a₂ * Real.cos (3 * θ) +
    fordTrigB4 * Real.cos (4 * θ)

theorem fordTrigSum_eq_constant_add_oscillatory (a₁ a₂ θ : ℝ) :
    fordTrigSum a₁ a₂ θ =
      fordTrigB0 a₁ a₂ + fordTrigOscillatory a₁ a₂ θ := by
  simp only [fordTrigSum, fordTrigOscillatory]
  ring

/-- The pointwise inequality used in Ford's proof of Lemma 5.1. -/
theorem ford_trigonometric_oscillatory_lower (a₁ a₂ θ : ℝ) :
    -fordTrigB0 a₁ a₂ ≤ fordTrigOscillatory a₁ a₂ θ := by
  have h := ford_trigonometric_nonneg a₁ a₂ θ
  rw [fordTrigSum_eq_constant_add_oscillatory] at h
  linarith

/-- A nonnegative Euler-product/Fourier weight preserves Ford's lower bound. -/
theorem ford_weighted_trigonometric_lower
    (a₁ a₂ θ q U : ℝ) (hq : 0 ≤ q) (hU : 0 ≤ U) :
    -fordTrigB0 a₁ a₂ * (q * U) ≤
      q * U * fordTrigOscillatory a₁ a₂ θ := by
  have hWeight : 0 ≤ q * U := mul_nonneg hq hU
  have h := mul_le_mul_of_nonneg_left
    (ford_trigonometric_oscillatory_lower a₁ a₂ θ) hWeight
  nlinarith

theorem fordTrigB0_eq_sum_squares (a₁ a₂ : ℝ) :
    fordTrigB0 a₁ a₂ =
      1 + 4 * (a₁ + a₂) ^ 2 + 2 * (2 * a₁ * a₂ + 1) ^ 2 := by
  simp only [fordTrigB0, fordTrigB2]
  ring

theorem fordTrigB0_one_le (a₁ a₂ : ℝ) :
    1 ≤ fordTrigB0 a₁ a₂ := by
  rw [fordTrigB0_eq_sum_squares]
  nlinarith [sq_nonneg (a₁ + a₂), sq_nonneg (2 * a₁ * a₂ + 1)]

theorem fordTrigB0_pos (a₁ a₂ : ℝ) :
    0 < fordTrigB0 a₁ a₂ :=
  zero_lt_one.trans_le (fordTrigB0_one_le a₁ a₂)

end GafniTao
