import Dubon2026.PrimeWittIntertwinerFrobenius

/-! # The actual natural uniformizer intertwining identity

For a natural unit a, the two proved semilinear identities combine to
intertwine upX+X^p with the explicit multiplicative scalar polynomial
(1+X)^(ap)-1. This is the exact identity to iterate at the actual primitive
p-power point in order to prove DUB-17's changed primitive polynomial.
-/
namespace Dubon2026
noncomputable section

/-- Composition of the explicit natural multiplicative scalar polynomials multiplies their original indices. -/
theorem primeWittNaturalSeries_compose (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    PowerSeries.subst (primeWittNaturalSeries p a) (primeWittNaturalSeries p b) =
      primeWittNaturalSeries p (a * b) := by
  rw [primeWittNaturalSeries_subst p b _
    (PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittNaturalSeries_constantCoeff p a))]
  simp only [primeWittNaturalSeries, ← add_sub_assoc, add_sub_cancel_left, ← pow_mul]

/-- The actual constructed series intertwines the changed prime polynomial and the explicit natural scalar ap polynomial. -/
theorem primeWittIntertwiner_natural_functional
    (p : ℕ) [Fact p.Prime] (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)
    (a : ℕ) (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    PowerSeries.subst (primeWittIntertwiner p u) (primeWittChangedSeries p u) =
      PowerSeries.subst (primeWittNaturalSeries p (p * a)) (primeWittIntertwiner p u) := by
  rw [primeWittIntertwiner_functionalEquation, primeWittIntertwiner_frobenius_nat p u a hu]
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittNaturalSeries_constantCoeff p a))
    (primeWittMultiplicativeSeries_hasSubst p)]
  change PowerSeries.subst
    (PowerSeries.subst (primeWittNaturalSeries p p) (primeWittNaturalSeries p a)) _ = _
  rw [primeWittNaturalSeries_compose]

end
end Dubon2026
