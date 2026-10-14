import Dubon2026.WittCyclotomicEvaluation
import Dubon2026.PrimeWittIntertwinerFrobenius

/-! # The actual changed point and its analytic inverse

Evaluate the constructed semilinear series at the actual cyclotomic root.
The proved substitution identities supply its analytic inverse and hence
injectivity on convergent points. This preserves primitive torsion when
constructing DUB-17's auxiliary uniformizer, rather than assuming an
invertible evaluated comparison map.
-/
namespace Dubon2026
noncomputable section
open scoped PowerSeries.WithPiTopology
attribute [local instance] wittCyclotomicCoefficientUniformSpace wittCyclotomicRootWithIdeal
  wittCyclotomicRootCompleteSpace wittCyclotomicRootT2Space

/-- The actual inverse series undoes the actual evaluated intertwiner at every convergent point. -/
theorem wittCyclotomicIntertwiner_eval_inverse
    (p : ℕ) [Fact p.Prime] (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n : ℕ) (x : wittCyclotomicRootAlgebra p n) (hx : PowerSeries.HasEval x) :
    wittCyclotomicPowerSeriesEval p n (wittCyclotomicPowerSeriesEval p n x hx (primeWittIntertwiner p u))
        (wittCyclotomicPowerSeriesEval_hasEval p n x hx _ (primeWittIntertwiner_hasSubst p u))
        (primeWittIntertwinerInverse p u) = x := by
  rw [← wittCyclotomicPowerSeriesEval_subst p n x hx _ _ (primeWittIntertwiner_hasSubst p u),
    primeWittIntertwinerInverse_left, wittCyclotomicPowerSeriesEval_X]

/-- The evaluated actual intertwiner is injective on genuine convergent points. -/
theorem wittCyclotomicIntertwiner_eval_injective
    (p : ℕ) [Fact p.Prime] (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (n : ℕ) (x y : wittCyclotomicRootAlgebra p n)
    (hx : PowerSeries.HasEval x) (hy : PowerSeries.HasEval y)
    (hxy : wittCyclotomicPowerSeriesEval p n x hx (primeWittIntertwiner p u) =
      wittCyclotomicPowerSeriesEval p n y hy (primeWittIntertwiner p u)) : x = y := by
  have h := congrArg (fun z : wittCyclotomicRootAlgebra p n =>
    PowerSeries.eval₂ (algebraMap (WittVector p (AlgebraicClosure (ZMod p)))
      (wittCyclotomicRootAlgebra p n)) z (primeWittIntertwinerInverse p u)) hxy
  have hx' := wittCyclotomicIntertwiner_eval_inverse p u n x hx
  have hy' := wittCyclotomicIntertwiner_eval_inverse p u n y hy
  simp only [wittCyclotomicPowerSeriesEval, PowerSeries.coe_eval₂Hom] at hx' hy' h
  exact hx'.symm.trans (h.trans hy')

/-- The actual changed point obtained from the original translated cyclotomic root. -/
def wittCyclotomicChangedPoint (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) : wittCyclotomicRootAlgebra p n :=
  wittCyclotomicPowerSeriesEval p n _ (wittCyclotomicRoot_hasEval p n) (primeWittIntertwiner p u)

/-- The constructed changed point is itself a genuine convergent point. -/
theorem wittCyclotomicChangedPoint_hasEval (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    PowerSeries.HasEval (wittCyclotomicChangedPoint p u n) :=
  wittCyclotomicPowerSeriesEval_hasEval p n _ (wittCyclotomicRoot_hasEval p n) _
    (primeWittIntertwiner_hasSubst p u)

/-- The actual inverse evaluation recovers the original cyclotomic root from the constructed changed point. -/
theorem wittCyclotomicChangedPoint_inverse (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (n : ℕ) :
    wittCyclotomicPowerSeriesEval p n (wittCyclotomicChangedPoint p u n)
      (wittCyclotomicChangedPoint_hasEval p u n) (primeWittIntertwinerInverse p u) =
      AdjoinRoot.root (primePowerShiftedCyclotomic (WittVector p (AlgebraicClosure (ZMod p))) p n) :=
  wittCyclotomicIntertwiner_eval_inverse p u n _ (wittCyclotomicRoot_hasEval p n)

end
end Dubon2026
