import Dubon2026.WittCyclotomicNaturalIntertwining
import Dubon2026.WittCyclotomicPrimitiveRoot
import Dubon2026.PrimeChangedDivisionPolynomial

/-! # Iterated changed torsion in the actual cyclotomic root algebra

The convergent intertwiner carries the exact natural multiplicative orbit
of the original root to the iterates of the changed polynomial. Its inverse
then detects exact primitive level. This supplies the annihilating polynomial
needed for the auxiliary normed uniformizer on DUB-17's reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology
attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space wittCyclotomicRootDomain

/-- The actual intertwiner sends zero to zero under convergent evaluation. -/
theorem wittCyclotomicIntertwiner_eval_zero (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    wittCyclotomicPowerSeriesEval p n 0 PowerSeries.HasEval.zero
      (primeWittIntertwiner p u) = 0 := by
  obtain ⟨A, hA⟩ := PowerSeries.X_dvd_iff.mpr (primeWittIntertwiner_constantCoeff p u)
  rw [hA, map_mul, wittCyclotomicPowerSeriesEval_X, zero_mul]

/-- Every actual changed-polynomial iterate is the intertwined original natural power. -/
theorem wittCyclotomicIntertwiner_eval_iterate (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) (k : ℕ) :
    (primeChangedPolynomialIterate p (u.val * p) k).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n))
      (wittCyclotomicPowerSeriesEval p n x hx (primeWittIntertwiner p u)) =
    wittCyclotomicPowerSeriesEval p n ((1 + x) ^ ((p * a) ^ k) - 1)
      (wittCyclotomicNaturalPoint_hasEval p n ((p * a) ^ k) x hx)
      (primeWittIntertwiner p u) := by
  induction k with
  | zero => simp only [primeChangedPolynomialIterate_zero, Polynomial.eval₂_X,
      pow_zero, pow_one, add_sub_cancel_left]
  | succ k ih =>
    rw [primeChangedPolynomialIterate_succ, Polynomial.eval₂_comp, ih]
    simp only [primeChangedPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    rw [add_comm, wittCyclotomicIntertwiner_eval_natural_step p n u a hu]
    simp only [← add_sub_assoc, add_sub_cancel_left, ← pow_mul, ← pow_succ]

/-- The constructed changed point is killed by the actual level n+1 iterate. -/
theorem wittCyclotomicChangedPoint_iterate_zero (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    (primeChangedPolynomialIterate p (u.val * p) (n + 1)).eval₂
      (algebraMap _ (wittCyclotomicRootAlgebra p n)) (wittCyclotomicChangedPoint p u n) = 0 := by
  rw [wittCyclotomicChangedPoint, wittCyclotomicIntertwiner_eval_iterate p u n a hu]
  have hpow : (wittCyclotomicPrimitiveRoot p n) ^ ((p * a) ^ (n + 1)) = 1 := by
    apply (wittCyclotomicPrimitiveRoot_isPrimitive p n).pow_eq_one_iff_dvd _ |>.mpr
    rw [mul_pow]
    exact dvd_mul_right _ _
  change (1 + AdjoinRoot.root (primePowerShiftedCyclotomic
    (WittVector p (AlgebraicClosure (ZMod p))) p n)) ^ ((p * a) ^ (n + 1)) = 1 at hpow
  simp only [hpow, sub_self]
  exact wittCyclotomicIntertwiner_eval_zero p u n

end
end Dubon2026
