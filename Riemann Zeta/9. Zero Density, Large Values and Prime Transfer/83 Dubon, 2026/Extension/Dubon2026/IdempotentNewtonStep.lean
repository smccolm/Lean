import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Module.NatInt

/-! # Exact polynomial improvement used to lift genuine matrix idempotents -/

namespace Dubon2026

variable {R S : Type*} [Ring R] [Ring S]

/-- The actual cubic polynomial whose iteration improves an original approximate idempotent. -/
def idempotentNewtonStep (x : R) : R := 3 * x ^ 2 - 2 * x ^ 3

/-- The change in the original matrix or ring element is a multiple of its genuine idempotency error. -/
theorem idempotentNewtonStep_sub (x : R) :
    idempotentNewtonStep x - x = (1 - 2 * x) * (x ^ 2 - x) := by
  unfold idempotentNewtonStep
  noncomm_ring

/-- The new actual idempotency error is divisible by the square of the original error, in an arbitrary associative ring, including the full matrix ring. -/
theorem idempotentNewtonStep_error (x : R) :
    (idempotentNewtonStep x) ^ 2 - idempotentNewtonStep x =
      (x ^ 2 - x) ^ 2 * (4 * (x ^ 2 - x) - 3) := by
  unfold idempotentNewtonStep
  noncomm_ring

/-- The genuine polynomial improvement commutes with every original coefficient ring homomorphism. -/
theorem idempotentNewtonStep_map (f : R →+* S) (x : R) :
    f (idempotentNewtonStep x) = idempotentNewtonStep (f x) := by
  simp only [idempotentNewtonStep, map_sub, map_mul, map_ofNat, map_pow]

end Dubon2026
