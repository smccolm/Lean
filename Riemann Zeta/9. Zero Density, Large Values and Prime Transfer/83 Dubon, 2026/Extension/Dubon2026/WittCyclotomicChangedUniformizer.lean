import Dubon2026.WittCyclotomicRootDVR
import Dubon2026.WittCyclotomicIntertwinerEvaluation

/-! # The actual changed point is a uniformizer of the cyclotomic root ring

Zero constant coefficients imply divisibility after genuine evaluation.
The constructed inverse gives divisibility in the opposite direction.
Thus the actual changed point is associated to the original cyclotomic
uniformizer. No new valuation estimate or assumed uniformizer is needed
for this step of DUB-17's auxiliary ramification comparison.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology
attribute [local instance] wittCyclotomicRootDomain wittCyclotomicRootDVR
  wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space

/-- The actual changed point is associated to the original translated cyclotomic root. -/
theorem wittCyclotomicChangedPoint_associated_root (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    Associated (wittCyclotomicChangedPoint p u n)
      (AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n)) := by
  apply associated_of_dvd_dvd
  · have h := map_dvd (wittCyclotomicPowerSeriesEval p n (wittCyclotomicChangedPoint p u n)
      (wittCyclotomicChangedPoint_hasEval p u n))
      (PowerSeries.X_dvd_iff.mpr (primeWittIntertwinerInverse_constantCoeff p u))
    simpa only [wittCyclotomicPowerSeriesEval_X, wittCyclotomicChangedPoint_inverse] using h
  · have h := map_dvd (wittCyclotomicPowerSeriesEval p n _ (wittCyclotomicRoot_hasEval p n))
      (PowerSeries.X_dvd_iff.mpr (primeWittIntertwiner_constantCoeff p u))
    simpa only [wittCyclotomicPowerSeriesEval_X, wittCyclotomicChangedPoint] using h

/-- The actual evaluated changed point is a genuine uniformizer of the actual cyclotomic root ring. -/
theorem wittCyclotomicChangedPoint_irreducible (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    Irreducible (wittCyclotomicChangedPoint p u n) := by
  exact (wittCyclotomicChangedPoint_associated_root p u n).irreducible_iff.mpr
    (wittCyclotomicRoot_irreducible p n)

end
end Dubon2026
