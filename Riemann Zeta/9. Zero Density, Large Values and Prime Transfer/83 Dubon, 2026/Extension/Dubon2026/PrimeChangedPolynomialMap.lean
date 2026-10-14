import Dubon2026.PrimeChangedDivisionPolynomial

/-! # Literal coefficient transport for the required primitive polynomial

The actual changed polynomial, its iterates and primitive quotient commute
with the original coefficient embeddings. These identities transport the
proved Witt primitive-point equation to the original rational completion,
so DUB-17's auxiliary finite field can be defined directly from that point.
-/
namespace Dubon2026
noncomputable section
open Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Mapping coefficients preserves the actual two-term changed polynomial. -/
theorem primeChangedPolynomial_map (f : R →+* S) (p : ℕ) (π : R) :
    (primeChangedPolynomial p π).map f = primeChangedPolynomial p (f π) := by
  simp [primeChangedPolynomial]

/-- Mapping coefficients preserves every actual changed iterate. -/
theorem primeChangedPolynomialIterate_map (f : R →+* S) (p : ℕ) (π : R) (n : ℕ) :
    (primeChangedPolynomialIterate p π n).map f = primeChangedPolynomialIterate p (f π) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [primeChangedPolynomialIterate_succ, Polynomial.map_comp,
      primeChangedPolynomial_map, ih, primeChangedPolynomialIterate_succ]

/-- The primitive changed polynomial commutes with the original coefficient map. -/
theorem primeChangedPrimitivePolynomial_map (f : R →+* S) (p : ℕ) (π : R) (n : ℕ) :
    (primeChangedPrimitivePolynomial p π n).map f = primeChangedPrimitivePolynomial p (f π) n := by
  simp only [primeChangedPrimitivePolynomial, Polynomial.map_add, Polynomial.map_pow,
    primeChangedPolynomialIterate_map, Polynomial.map_C]

end
end Dubon2026
