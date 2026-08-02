import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

noncomputable section

namespace EllipseOmega

/-!
# THE MASTER BLUEPRINT: A Mechanized Ellipse Perimeter
## MODULE A: Combinatorics and the Wallis Sequence

Purpose: Establish the integer-ratio sequences that drive both the binomial
expansion and the integrated sine powers. We do this entirely in ℝ (via
`Nat.cast`) to avoid later coercion hell.
-/

-- 1. Definitions Required:

/--
Wallis Even Coefficient (`w_n`):
mathematically `w_n = (2n)! / (2^{2n} (n!)^2)`.
-/
def wallisEvenCoeff (n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ) /
    (((2 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2)

/--
Square Root Coefficient (`a_n`):
mathematically `a_n = w_n / (1 - 2n)`.
-/
def sqrtOneSubCoeff (n : ℕ) : ℝ :=
  wallisEvenCoeff n * (1 / (1 - 2 * (n : ℝ)))

/--
Elliptic Coefficient (`c_n`):
mathematically `c_n = a_n * w_n = w_n^2 / (1 - 2n)`.
-/
def ellipticESeriesCoeff (n : ℕ) : ℝ :=
  ((((2 * n).factorial : ℝ) /
      (((2 : ℝ) ^ n * (n.factorial : ℝ)) ^ 2)) ^ 2) *
    (1 / (1 - 2 * (n : ℝ)))


-- 3. Traps for the LLM to Avoid:

theorem two_mul_natCast_ne_one (n : ℕ) :
    (2 * (n : ℝ)) ≠ 1 := by
  intro h
  have hnat : 2 * n = 1 := by exact_mod_cast h
  omega

theorem one_sub_two_natCast_ne_zero (n : ℕ) :
    1 - 2 * (n : ℝ) ≠ 0 := by
  intro h
  have h' : 2 * (n : ℝ) = 1 := by linarith
  exact two_mul_natCast_ne_one n h'


-- 2. The Algebraic Recurrences:

/--
You must prove the n -> n + 1 recurrence for w_n.
The ratio is exactly (2n+1)/(2n+2).
-/
theorem wallisEvenCoeff_succ (n : ℕ) :
    wallisEvenCoeff (n + 1) =
      ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) * wallisEvenCoeff n := by
  unfold wallisEvenCoeff
  have hfac :
      ((2 * (n + 1)).factorial : ℝ) =
        (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * ((2 * n).factorial : ℝ) := by
    have h1 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw[h1, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hden :
      (2 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ) =
        (2 * (n : ℝ) + 2) * ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
    rw[pow_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac, hden]
  have hne1 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  have hne2 : (2 : ℝ) ^ n * (n.factorial : ℝ) ≠ 0 := by positivity
  have hne3 :
      (2 * (n : ℝ) + 2) * ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≠ 0 := by
    exact mul_ne_zero hne1 hne2
  field_simp[hne1, hne2, hne3]

/--
You must prove the recurrence for a_n.
The ratio is exactly (2n-1)/(2n+2).
-/
theorem sqrtOneSubCoeff_succ (n : ℕ) :
    sqrtOneSubCoeff (n + 1) =
      ((2 * (n : ℝ) - 1) / (2 * (n : ℝ) + 2)) * sqrtOneSubCoeff n := by
  unfold sqrtOneSubCoeff
  rw[wallisEvenCoeff_succ]
  have hs :
      1 - 2 * ((n + 1 : ℕ) : ℝ) = -(2 * (n : ℝ) + 1) := by
    push_cast
    ring
  rw [hs]
  have hne1 : 1 - 2 * (n : ℝ) ≠ 0 := one_sub_two_natCast_ne_zero n
  have hne2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  have hne3 : -(2 * (n : ℝ) + 1) ≠ 0 := by
    intro h
    have : 2 * (n : ℝ) + 1 = 0 := neg_eq_zero.mp h
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  field_simp [hne1, hne2, hne3]
  ring

theorem ellipticESeriesCoeff_eq_mul (n : ℕ) :
    ellipticESeriesCoeff n = sqrtOneSubCoeff n * wallisEvenCoeff n := by
  unfold ellipticESeriesCoeff sqrtOneSubCoeff wallisEvenCoeff
  ring

/--
You must prove the recurrence for c_n.
The ratio is exactly (2n-1)(2n+1)/(2n+2)^2.
-/
theorem ellipticESeriesCoeff_succ (n : ℕ) :
    ellipticESeriesCoeff (n + 1) =
      (((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1)) / (2 * (n : ℝ) + 2) ^ 2) *
        ellipticESeriesCoeff n := by
  have h1 : ellipticESeriesCoeff (n + 1) =
      sqrtOneSubCoeff (n + 1) * wallisEvenCoeff (n + 1) := by
    exact ellipticESeriesCoeff_eq_mul (n + 1)
  have h2 : ellipticESeriesCoeff n =
      sqrtOneSubCoeff n * wallisEvenCoeff n := by
    exact ellipticESeriesCoeff_eq_mul n
  rw [h1, h2]
  rw[sqrtOneSubCoeff_succ, wallisEvenCoeff_succ]
  have hne : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hne]

end EllipseOmega
