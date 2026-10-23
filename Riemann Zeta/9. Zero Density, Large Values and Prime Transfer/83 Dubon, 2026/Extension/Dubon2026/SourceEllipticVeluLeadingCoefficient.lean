import Dubon2026.SourceEllipticVeluQuadraticDegrees
import Dubon2026.SourceEllipticVeluCubicDifference

/-! The leading cubic coefficient of the actual Velu relation is minus one.
Adapted from TauCeti Isogeny/Velu/Equation.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba. The actual square-minus-cube
bound rules out a cubic remainder. This supplies the leading coefficient
required by the explicit odd quotient equation on the DUB-17/18 chain. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {S : Finset (F × F)}
variable {p q : F[X]}

/-- The actual quadratic relation has the Weierstrass cubic leading coefficient. -/
theorem velu_relation_cubic_coeff
    (h : genericVeluY W S ^ 2 + aeval (genericVeluX W S) p * genericVeluY W S +
      aeval (genericVeluX W S) q = 0) : q.coeff 3 = -1 := by
  set X := genericVeluX W S
  set Y := genericVeluY W S
  obtain ⟨hqdeg, hpY⟩ := velu_relation_cubic_and_linear_value h
  by_contra hne
  set q' := q + Polynomial.X ^ 3
  have hq'3 : q'.coeff 3 ≠ 0 := by
    simp only [q', Polynomial.coeff_add, Polynomial.coeff_X_pow_self]
    exact fun h0 => hne (eq_neg_of_add_eq_zero_left h0)
  have hq'0 : q' ≠ 0 := fun h0 => hq'3 (by rw [h0, Polynomial.coeff_zero])
  have hq'deg : q'.natDegree = 3 :=
    le_antisymm ((Polynomial.natDegree_add_le _ _).trans (by simp [hqdeg]))
      (Polynomial.le_natDegree_of_ne_zero hq'3)
  have hv := infinityValuation_aeval_mul_add W S (p := p) hq'0
  rw [hq'deg, max_eq_right (hpY.trans (WithZero.exp_le_exp.mpr (by norm_num)))] at hv
  have hsub : aeval X p * Y + aeval X q' = -(Y ^ 2 - X ^ 3) := by
    simp only [q', map_add, map_pow, Polynomial.aeval_X]
    linear_combination h
  rw [hsub, Valuation.map_neg] at hv
  have hb := infinityValuation_velu_square_sub_cube_le W S
  rw [hv, WithZero.exp_le_exp] at hb
  norm_num at hb

end Dubon2026.SourceEllipticFunctionField
