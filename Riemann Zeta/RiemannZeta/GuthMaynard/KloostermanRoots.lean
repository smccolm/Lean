import RiemannZeta.GuthMaynard.KloostermanCurveTrace
import Mathlib.Analysis.RCLike.Sqrt

/-!
# The two local Kloosterman roots

This module formalizes Harcos equation (2) with an explicit quadratic-formula
choice of the two complex roots.
-/

namespace RiemannZeta.GuthMaynard

theorem complex_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num)

/-- The `kloostermanAlpha` definition used by the source-facing construction in `KloostermanRoots`. -/
noncomputable def kloostermanAlpha (p : ℕ) [NeZero p]
    (A B : ZMod p) : ℂ :=
  let S := kloostermanSumZMod p A B
  (-S + Complex.sqrt (S ^ 2 - 4 * p)) / 2

/-- The `kloostermanBeta` definition used by the source-facing construction in `KloostermanRoots`. -/
noncomputable def kloostermanBeta (p : ℕ) [NeZero p]
    (A B : ZMod p) : ℂ :=
  let S := kloostermanSumZMod p A B
  (-S - Complex.sqrt (S ^ 2 - 4 * p)) / 2

theorem kloostermanAlpha_add_beta (p : ℕ) [NeZero p]
    (A B : ZMod p) :
    kloostermanAlpha p A B + kloostermanBeta p A B =
      -kloostermanSumZMod p A B := by
  simp [kloostermanAlpha, kloostermanBeta]
  ring

theorem kloostermanAlpha_mul_beta (p : ℕ) [NeZero p]
    (A B : ZMod p) :
    kloostermanAlpha p A B * kloostermanBeta p A B = (p : ℂ) := by
  rw [kloostermanAlpha, kloostermanBeta]
  have hs := complex_sqrt_sq
    (kloostermanSumZMod p A B ^ 2 - 4 * (p : ℂ))
  field_simp
  linear_combination -hs

/-- Harcos equation (2), as an identity at every complex `T`. -/
theorem kloostermanEquationTwo (p : ℕ) [NeZero p]
    (A B : ZMod p) (T : ℂ) :
    1 + kloostermanSumZMod p A B * T + p * T ^ 2 =
      (1 - kloostermanAlpha p A B * T) *
        (1 - kloostermanBeta p A B * T) := by
  rw [show kloostermanSumZMod p A B =
    -(kloostermanAlpha p A B + kloostermanBeta p A B) by
      rw [kloostermanAlpha_add_beta]; simp]
  rw [← kloostermanAlpha_mul_beta p A B]
  ring

end RiemannZeta.GuthMaynard
