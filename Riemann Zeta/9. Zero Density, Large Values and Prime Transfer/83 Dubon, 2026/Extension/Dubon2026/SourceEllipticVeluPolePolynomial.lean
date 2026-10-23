import Dubon2026.SourceEllipticVeluInfinityY

/-! Values of polynomial expressions in the actual Velu coordinates.
Adapted from TauCeti Isogeny/Velu/Equation.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba. The proved double and triple
poles distinguish even and odd orders; this supplies the polynomial-degree
bounds for the explicit odd quotient relation on the DUB-17/18 chain. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (S : Finset (F × F))

/-- The actual Velu y-coordinate is nonzero, as witnessed by its triple pole. -/
theorem genericVeluY_ne_zero : genericVeluY W S ≠ 0 := by
  intro h
  have hv := infinityValuation_genericVeluY W S
  rw [h, map_zero] at hv
  exact WithZero.exp_ne_zero hv.symm

/-- A nonzero polynomial in the literal quotient x-coordinate has twice its degree as pole order. -/
theorem infinityValuation_aeval_genericVeluX {p : F[X]} (hp : p ≠ 0) :
    infinityValuation W.toAffine (aeval (genericVeluX W S) p) =
      WithZero.exp (2 * p.natDegree : ℤ) := by
  letI := infinityValuation_trivial W.toAffine
  rw [Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      (v := infinityValuation W.toAffine) _ ?_ hp,
    infinityValuation_genericVeluX, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_comm]
  rw [infinityValuation_genericVeluX, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/-- The polynomial and y-linear terms have distinct pole-order parity, so their values cannot cancel. -/
theorem infinityValuation_aeval_mul_add {p q : F[X]} (hq : q ≠ 0) :
    infinityValuation W.toAffine
        (aeval (genericVeluX W S) p * genericVeluY W S + aeval (genericVeluX W S) q) =
      max (infinityValuation W.toAffine (aeval (genericVeluX W S) p * genericVeluY W S))
        (WithZero.exp (2 * q.natDegree : ℤ)) := by
  rw [← infinityValuation_aeval_genericVeluX W S hq]
  refine Valuation.map_add_of_distinct_val _ ?_
  rw [infinityValuation_aeval_genericVeluX W S hq]
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using WithZero.exp_ne_zero.symm
  · rw [map_mul, infinityValuation_aeval_genericVeluX W S hp,
      infinityValuation_genericVeluY, ← WithZero.exp_add, Ne, WithZero.exp_inj]
    omega

end Dubon2026.SourceEllipticFunctionField
