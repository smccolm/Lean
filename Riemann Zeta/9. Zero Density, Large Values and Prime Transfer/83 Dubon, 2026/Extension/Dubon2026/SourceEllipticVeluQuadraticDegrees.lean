import Dubon2026.SourceEllipticVeluPolePolynomial

/-! Exact degree bounds in the actual Velu quadratic relation. Adapted from
TauCeti Isogeny/Velu/Equation.lean, Apache-2.0, commit
bfcff79b60964ba7bdb78b952828313686c327ba. The proved literal-coordinate
pole orders force degree at most one for the y coefficient and degree three
for the constant polynomial. These are equation coefficient obligations on
the DUB-17/18 chain; the actual relation is supplied by the fixed-field proof. -/

open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
open scoped Classical

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {S : Finset (F × F)}
variable {p q : F[X]}
variable (h : genericVeluY W S ^ 2 + aeval (genericVeluX W S) p * genericVeluY W S +
  aeval (genericVeluX W S) q = 0)
include h

/-- The constant polynomial in the actual quadratic relation cannot vanish. -/
theorem velu_relation_constant_ne_zero : q ≠ 0 := by
  set X := genericVeluX W S
  set Y := genericVeluY W S
  rintro rfl
  have hY0 : Y ≠ 0 := genericVeluY_ne_zero W S
  have hYp : Y + aeval X p = 0 := by
    have h' : Y ^ 2 + aeval X p * Y = 0 := by simpa using h
    have he : Y * (Y + aeval X p) = 0 := by linear_combination h'
    exact (mul_eq_zero.mp he).resolve_left hY0
  rcases eq_or_ne p 0 with rfl | hp
  · exact hY0 (by simpa using hYp)
  · have hv : infinityValuation W.toAffine Y = infinityValuation W.toAffine (aeval X p) := by
      rw [eq_neg_of_add_eq_zero_left hYp, Valuation.map_neg]
    rw [infinityValuation_genericVeluY, infinityValuation_aeval_genericVeluX W S hp,
      WithZero.exp_inj] at hv
    omega

/-- The actual relation's constant polynomial is cubic and its y-linear term has pole at most five. -/
theorem velu_relation_cubic_and_linear_value :
    q.natDegree = 3 ∧
      infinityValuation W.toAffine (aeval (genericVeluX W S) p * genericVeluY W S) ≤
        WithZero.exp 5 := by
  set X := genericVeluX W S
  set Y := genericVeluY W S
  set v := infinityValuation W.toAffine
  have hq := velu_relation_constant_ne_zero h
  have hrel : v (aeval X p * Y + aeval X q) = WithZero.exp 6 := by
    rw [show aeval X p * Y + aeval X q = -(Y ^ 2) by linear_combination h,
      Valuation.map_neg, map_pow, infinityValuation_genericVeluY, ← WithZero.exp_nsmul]
    norm_num
  rw [infinityValuation_aeval_mul_add W S hq] at hrel
  rcases max_choice (v (aeval X p * Y)) (WithZero.exp (2 * q.natDegree : ℤ)) with hm | hm
  · rw [hm] at hrel
    rcases eq_or_ne p 0 with rfl | hp
    · simp only [map_zero, zero_mul] at hrel
      exact (WithZero.exp_ne_zero hrel.symm).elim
    · rw [map_mul, infinityValuation_aeval_genericVeluX W S hp,
        infinityValuation_genericVeluY, ← WithZero.exp_add, WithZero.exp_inj] at hrel
      omega
  · have hle := hm ▸ le_max_left (v (aeval X p * Y)) (WithZero.exp (2 * q.natDegree : ℤ))
    rw [hm, WithZero.exp_inj] at hrel
    refine ⟨by omega, ?_⟩
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    · rw [map_mul, infinityValuation_aeval_genericVeluX W S hp,
        infinityValuation_genericVeluY, ← WithZero.exp_add, WithZero.exp_le_exp] at hle ⊢
      omega

/-- The actual relation's y-coefficient polynomial has degree at most one. -/
theorem velu_relation_linear_degree_le : p.natDegree ≤ 1 := by
  have hle := (velu_relation_cubic_and_linear_value h).2
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [map_mul, infinityValuation_aeval_genericVeluX W S hp,
      infinityValuation_genericVeluY, ← WithZero.exp_add, WithZero.exp_le_exp] at hle
    omega

end Dubon2026.SourceEllipticFunctionField
