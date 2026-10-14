import Dubon2026.PrimeWittIntertwiner
import Dubon2026.PowerSeriesLinearSubstitution

/-! # Explicit natural scalar series on the required cyclotomic route

The principal-product argument concerns rational units. For positive
integer units the multiplicative scalar series is the explicit polynomial
(1+X)^a-1. Its commutation and Frobenius identities suffice to compare the
constructed intertwiner, without general Lubin--Tate scalar endomorphisms.
-/
namespace Dubon2026
noncomputable section
variable (p : ℕ) [Fact p.Prime]

/-- The actual natural scalar polynomial of the multiplicative formal group. -/
def primeWittNaturalSeries (a : ℕ) : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
  (1 + PowerSeries.X) ^ a - 1

/-- Its constant coefficient is zero. -/
theorem primeWittNaturalSeries_constantCoeff (a : ℕ) :
    PowerSeries.constantCoeff (primeWittNaturalSeries p a) = 0 := by
  simp [primeWittNaturalSeries]

/-- Its linear coefficient is the original natural number. -/
theorem primeWittNaturalSeries_coeff_one (a : ℕ) :
    PowerSeries.coeff 1 (primeWittNaturalSeries p a) = a := by
  simp [primeWittNaturalSeries, PowerSeries.coeff_one_pow]

/-- Actual Witt Frobenius fixes the natural scalar polynomial. -/
theorem primeWittNaturalSeries_frobenius (a : ℕ) :
    PowerSeries.map WittVector.frobenius (primeWittNaturalSeries p a) =
      primeWittNaturalSeries p a := by
  simp [primeWittNaturalSeries]

/-- Substitution in this actual polynomial is its usual polynomial evaluation. -/
theorem primeWittNaturalSeries_subst (a : ℕ)
    (g : PowerSeries (WittVector p (AlgebraicClosure (ZMod p)))) (hg : PowerSeries.HasSubst g) :
    PowerSeries.subst g (primeWittNaturalSeries p a) = (1 + g) ^ a - 1 := by
  rw [← PowerSeries.coe_substAlgHom hg]
  simp [primeWittNaturalSeries, PowerSeries.substAlgHom_X]

/-- The actual natural scalar polynomial commutes with the original multiplicative prime polynomial. -/
theorem primeWittNaturalSeries_commutes (a : ℕ) :
    PowerSeries.subst (primeWittNaturalSeries p a) (primeWittMultiplicativeSeries p) =
      PowerSeries.subst (primeWittMultiplicativeSeries p) (primeWittNaturalSeries p a) := by
  have ha := PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittNaturalSeries_constantCoeff p a)
  change PowerSeries.subst (primeWittNaturalSeries p a) (primeWittNaturalSeries p p) = _
  rw [primeWittNaturalSeries_subst p p _ ha,
    primeWittNaturalSeries_subst p a _ (primeWittMultiplicativeSeries_hasSubst p)]
  simp only [primeWittNaturalSeries, primeWittMultiplicativeSeries,
    ← add_sub_assoc, add_sub_cancel_left, ← pow_mul, mul_comm a p]

/-- The actual changed polynomial is Frobenius fixed when its unit is an original natural scalar. -/
theorem primeWittChangedSeries_frobenius_nat
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) (a : ℕ)
    (hu : (u : WittVector p (AlgebraicClosure (ZMod p))) = a) :
    PowerSeries.map WittVector.frobenius (primeWittChangedSeries p u) =
      primeWittChangedSeries p u := by
  simp [primeWittChangedSeries, hu]

end
end Dubon2026
