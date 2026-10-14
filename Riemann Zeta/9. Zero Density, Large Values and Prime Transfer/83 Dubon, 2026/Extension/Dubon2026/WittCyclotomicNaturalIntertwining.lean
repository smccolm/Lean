import Dubon2026.WittCyclotomicIntertwinerEvaluation
import Dubon2026.PrimeWittNaturalIntertwining

/-! # The actual evaluated natural-unit intertwining step

The original natural scalar series evaluates to (1+x)^a-1. Combine this
with the constructed semilinear identity to prove the changed prime step
on actual convergent points. Iteration will give the genuine primitive
polynomial of DUB-17's auxiliary uniformizer.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology
attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space

/-- The actual natural scalar series evaluates to its original explicit polynomial. -/
theorem wittCyclotomicNaturalSeries_eval (p : ℕ) [Fact p.Prime] (n a : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    wittCyclotomicPowerSeriesEval p n x hx (primeWittNaturalSeries p a) = (1 + x) ^ a - 1 := by
  rw [primeWittNaturalSeries, map_sub, map_pow, map_add, map_one, wittCyclotomicPowerSeriesEval_X]

/-- The explicit scalar polynomial sends actual convergent points to actual convergent points. -/
theorem wittCyclotomicNaturalPoint_hasEval (p : ℕ) [Fact p.Prime] (n a : ℕ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    PowerSeries.HasEval ((1 + x) ^ a - 1) := by
  rw [← wittCyclotomicNaturalSeries_eval p n a x hx]
  exact wittCyclotomicPowerSeriesEval_hasEval p n x hx _
    (PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittNaturalSeries_constantCoeff p a))

/-- The actual changed prime series evaluates to the actual changed polynomial. -/
theorem wittCyclotomicChangedSeries_eval (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    wittCyclotomicPowerSeriesEval p n x hx (primeWittChangedSeries p u) =
      algebraMap _ (wittCyclotomicRootAlgebra p n) (u.val * p) * x + x ^ p := by
  rw [primeWittChangedSeries, map_add, map_mul, map_pow, wittCyclotomicPowerSeriesEval_X]
  rw [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

/-- The evaluated actual intertwiner carries the multiplicative natural ap step to the actual changed prime step. -/
theorem wittCyclotomicIntertwiner_eval_natural_step (p : ℕ) [Fact p.Prime] (n : ℕ)
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a)
    (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    let y := wittCyclotomicPowerSeriesEval p n x hx (primeWittIntertwiner p u)
    algebraMap _ (wittCyclotomicRootAlgebra p n) (u.val * p) * y + y ^ p =
      wittCyclotomicPowerSeriesEval p n ((1 + x) ^ (p * a) - 1)
        (wittCyclotomicNaturalPoint_hasEval p n (p * a) x hx) (primeWittIntertwiner p u) := by
  have h := congrArg (wittCyclotomicPowerSeriesEval p n x hx)
    (primeWittIntertwiner_natural_functional p u a hu)
  rw [wittCyclotomicPowerSeriesEval_subst p n x hx _ _ (primeWittIntertwiner_hasSubst p u),
    wittCyclotomicChangedSeries_eval,
    wittCyclotomicPowerSeriesEval_subst p n x hx _ _
      (PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittNaturalSeries_constantCoeff p (p * a)))] at h
  simpa only [wittCyclotomicNaturalSeries_eval] using h

end
end Dubon2026
