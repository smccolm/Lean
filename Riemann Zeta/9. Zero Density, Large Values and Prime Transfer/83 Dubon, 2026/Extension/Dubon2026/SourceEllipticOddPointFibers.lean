import Dubon2026.SourceEllipticOddPointSurjective
import Mathlib.Data.ZMod.QuotientGroup

/-! Exact sizes of the actual odd quotient kernel and every point fiber.
The proved cyclic kernel and surjectivity reduce the count to the native
cardinality of integer multiples and translation of a fiber. These are
the finite quotient-map inputs to the odd-prime modular-polynomial product
and cyclic-subgroup correspondence required by DUB-17/18. -/

open WeierstrassCurve
open Dubon2026.SourceEllipticVelu

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F)
variable [W.IsElliptic] {Q : W.toAffine.Point} {n : ℕ}

/-- The actual odd quotient kernel has exactly the order of the specified cyclic subgroup. -/
theorem card_ker_oddPointNorm (hQ : addOrderOf Q = 2 * n + 1) :
    Nat.card (oddPointNorm W hQ).ker = 2 * n + 1 := by
  rw [ker_oddPointNorm, Nat.card_zmultiples, hQ]

/-- Every actual point fiber of the odd quotient has exactly the specified odd order. -/
theorem card_fiber_oddPointNorm (hQ : addOrderOf Q = 2 * n + 1)
    (R : (veluQuotient W (oddOrderSummingSet W Q n)).toAffine.Point) :
    Nat.card {P : W.toAffine.Point // oddPointNorm W hQ P = R} = 2 * n + 1 := by
  obtain ⟨P₀, hP₀⟩ := oddPointNorm_surjective W hQ R
  have e : (oddPointNorm W hQ).ker ≃ {P : W.toAffine.Point // oddPointNorm W hQ P = R} := by
    refine Equiv.subtypeEquiv (Equiv.addRight P₀) fun P => ?_
    change oddPointNorm W hQ P = 0 ↔ oddPointNorm W hQ (P + P₀) = R
    rw [map_add, hP₀]
    exact add_eq_right.symm
  exact (Nat.card_congr e).symm.trans (card_ker_oddPointNorm W hQ)

end Dubon2026.SourceEllipticFunctionField
