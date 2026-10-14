import Mathlib.RingTheory.Norm.Basic

/-! # The exact norm of a negative power-basis generator

This direct consequence of the pinned norm formula lets the actual
original auxiliary-field consumer compute its norm without repeatedly
unfolding the concrete field and scalar-tower definitions.
-/
namespace Dubon2026
noncomputable section

/-- The negative generator norm is precisely the constant coefficient of its minimal polynomial. -/
theorem powerBasis_norm_neg_gen {K E : Type*} [Field K] [Field E] [Algebra K E]
    (b : PowerBasis K E) :
    Algebra.norm K (-b.gen) = (minpoly K b.gen).coeff 0 := by
  have hneg : Algebra.norm K (-1 : E) = (-1 : K) ^ b.dim := by
    rw [show (-1 : E) = algebraMap K E (-1) by simp, Algebra.norm_algebraMap, b.finrank]
  rw [← neg_one_mul b.gen, map_mul, hneg, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly,
    ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

end
end Dubon2026
