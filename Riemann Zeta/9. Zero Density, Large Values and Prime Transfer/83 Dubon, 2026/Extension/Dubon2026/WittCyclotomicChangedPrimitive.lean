import Dubon2026.WittCyclotomicChangedIterates
import Dubon2026.PrimeChangedPrimitiveEisenstein

/-! # Exact primitive level of the actual changed point

The original cyclotomic root has exact prime-power order, and the natural
unit is coprime to that prime. The proved convergent inverse therefore
prevents premature vanishing. The actual iterate factorization gives the
required primitive polynomial, without assuming primitive changed torsion.
This is the input to the auxiliary field norm used by DUB-17 reciprocity.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology
attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space wittCyclotomicRootDomain

/-- The preceding changed iterate does not vanish at the actual constructed point. -/
theorem wittCyclotomicChangedPoint_iterate_ne_zero (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    (primeChangedPolynomialIterate p (u.val * p) n).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n)) (wittCyclotomicChangedPoint p u n) ≠ 0 := by
  rw [wittCyclotomicChangedPoint, wittCyclotomicIntertwiner_eval_iterate p u n a hu]
  intro h
  have heq := wittCyclotomicIntertwiner_eval_injective p u n _ 0
    (wittCyclotomicNaturalPoint_hasEval p n ((p * a) ^ n) _ (wittCyclotomicRoot_hasEval p n))
    PowerSeries.HasEval.zero (h.trans (wittCyclotomicIntertwiner_eval_zero p u n).symm)
  have hz : (wittCyclotomicPrimitiveRoot p n) ^ ((p * a) ^ n) = 1 := sub_eq_zero.mp heq
  have hd := (wittCyclotomicPrimitiveRoot_isPrimitive p n).dvd_of_pow_eq_one _ hz
  rw [mul_pow, pow_succ] at hd
  exact ha ((Fact.out : p.Prime).dvd_of_dvd_pow
    (Nat.dvd_of_mul_dvd_mul_left (pow_pos (Fact.out : p.Prime).pos n) hd))

/-- The constructed actual point is a root of the exact primitive changed polynomial. -/
theorem wittCyclotomicChangedPoint_primitivePolynomial (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) (ha : ¬p ∣ a) :
    (primeChangedPrimitivePolynomial p (u.val * p) n).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n)) (wittCyclotomicChangedPoint p u n) = 0 := by
  have h := wittCyclotomicChangedPoint_iterate_zero p u n a hu
  rw [primeChangedPolynomialIterate_succ_factor, Polynomial.eval₂_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (wittCyclotomicChangedPoint_iterate_ne_zero p u n a hu ha)

end
end Dubon2026
