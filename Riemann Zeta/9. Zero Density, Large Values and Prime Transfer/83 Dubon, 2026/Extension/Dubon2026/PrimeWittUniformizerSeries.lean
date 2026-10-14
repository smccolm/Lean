import Dubon2026.PrimeWittFrobeniusRotation
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # The explicit Witt power series for the required change of uniformizer

The multiplicative series (1+X)^p-1 and changed series upX+X^p are the actual
source polynomials over the completed-unramified Witt coefficients. Their
zero constants, linear coefficients and identical reduction X^p supply the
coefficient recursion for the semilinear intertwiner. That construction is
needed for DUB-17's ramified cyclotomic reciprocity formula and then the
principal product, arithmetic invariant sum-zero and global duality.
-/
namespace Dubon2026
noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The actual multiplicative prime series over the Witt coefficient ring. -/
def primeWittMultiplicativeSeries :
    PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
  (1 + PowerSeries.X) ^ p - 1

/-- The actual changed-uniformizer polynomial upX+X^p over the same coefficients. -/
def primeWittChangedSeries (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
  PowerSeries.C (u.val * p) * PowerSeries.X + PowerSeries.X ^ p

/-- The original multiplicative series has zero constant coefficient. -/
theorem primeWittMultiplicativeSeries_constantCoeff :
    PowerSeries.constantCoeff (primeWittMultiplicativeSeries p) = 0 := by
  simp [primeWittMultiplicativeSeries]

/-- Its actual linear coefficient is the prime. -/
theorem primeWittMultiplicativeSeries_coeff_one :
    PowerSeries.coeff 1 (primeWittMultiplicativeSeries p) = p := by
  simp [primeWittMultiplicativeSeries, PowerSeries.coeff_one_pow]

/-- The changed series has zero constant coefficient. -/
theorem primeWittChangedSeries_constantCoeff (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.constantCoeff (primeWittChangedSeries p u) = 0 := by
  simp [primeWittChangedSeries, (Fact.out : p.Prime).ne_zero]

/-- Its actual linear coefficient is the changed uniformizer up. -/
theorem primeWittChangedSeries_coeff_one (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.coeff 1 (primeWittChangedSeries p u) = u.val * p := by
  simp [primeWittChangedSeries, PowerSeries.coeff_X_pow, (Fact.out : p.Prime).ne_one.symm]

/-- The multiplicative series admits genuine formal substitution. -/
theorem primeWittMultiplicativeSeries_hasSubst :
    PowerSeries.HasSubst (primeWittMultiplicativeSeries p) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittMultiplicativeSeries_constantCoeff p)

/-- The changed series admits genuine formal substitution. -/
theorem primeWittChangedSeries_hasSubst (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.HasSubst (primeWittChangedSeries p u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (primeWittChangedSeries_constantCoeff p u)

/-- The original multiplicative series reduces to the residue Frobenius monomial. -/
theorem primeWittMultiplicativeSeries_residue :
    PowerSeries.map WittVector.constantCoeff (primeWittMultiplicativeSeries p) =
      (PowerSeries.X : PowerSeries (AlgebraicClosure (ZMod p))) ^ p := by
  letI : CharP (PowerSeries (AlgebraicClosure (ZMod p))) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  simp only [primeWittMultiplicativeSeries, map_sub, map_pow, map_add, map_one,
    PowerSeries.map_X]
  rw [add_pow_char]
  simp

/-- The actual changed series has the identical residue Frobenius monomial. -/
theorem primeWittChangedSeries_residue (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    PowerSeries.map WittVector.constantCoeff (primeWittChangedSeries p u) =
      (PowerSeries.X : PowerSeries (AlgebraicClosure (ZMod p))) ^ p := by
  letI : CharP (PowerSeries (AlgebraicClosure (ZMod p))) p :=
    charP_of_injective_ringHom PowerSeries.C_injective p
  simp only [primeWittChangedSeries, map_add, map_mul, map_pow, PowerSeries.map_C,
    PowerSeries.map_X, map_natCast]
  rw [CharP.cast_eq_zero (PowerSeries (AlgebraicClosure (ZMod p))) p]
  simp

end
end Dubon2026
