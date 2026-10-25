import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! DUB-17/18 -> primitive projector. Absence of length-two zero Jordan
chains removes every higher zero power, as needed to reduce an actual
annihilating polynomial to a projector polynomial. -/
namespace Dubon2026
variable {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]

theorem end_pow_zero_implies_apply_zero (H : Module.End R V)
    (hH : ∀ x, H (H x) = 0 → H x = 0) (n : ℕ) (x : V)
    (hx : (H ^ n) x = 0) : H x = 0 := by
  induction n generalizing x with
  | zero => simpa only [pow_zero, Module.End.one_apply, map_zero] using congrArg H hx
  | succ n ih =>
      apply hH x
      apply ih (H x)
      simpa only [pow_succ, Module.End.mul_apply] using hx

end Dubon2026
