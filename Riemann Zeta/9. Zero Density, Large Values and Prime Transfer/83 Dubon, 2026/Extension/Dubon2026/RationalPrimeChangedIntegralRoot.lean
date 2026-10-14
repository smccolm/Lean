import Dubon2026.RationalPrimeOriginalUniformizer
import Dubon2026.PrimeChangedPrimitiveEisenstein
import Dubon2026.MonicEisensteinRootDVR

/-! # The actual changed-uniformizer integral root ring

The primitive changed polynomial is formed over the literal valuation
integers of the original rational-prime completion.  Its constant
coefficient is the original unit times the original prime.  Eisenstein
therefore gives a domain and a DVR, while the existing monic-root theorem
gives completeness.  This is the integral model for the local auxiliary
field required by DUB-17's ramified reciprocity argument.
-/
namespace Dubon2026
noncomputable section
open Polynomial IsLocalRing
open scoped ValuativeRel

/-- The exact changed primitive polynomial over the original valuation integers. -/
def rationalPrimeChangedIntegralPolynomial (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) : Polynomial 𝒪[rationalPrimeLocalField p hp] :=
  primeChangedPrimitivePolynomial p (u.val * p) n

/-- The displayed changed uniformizer is prime in the original valuation-integer ring. -/
theorem rationalPrimeChangedIntegralUniformizer_prime (p : ℕ) (hp : p.Prime)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) : Prime (u.val * p) :=
  prime_mul_iff.mpr
    (Or.inr ⟨u.isUnit, (rationalPrimeValuationInteger_irreducible_prime p hp).prime⟩)

/-- The actual changed integral polynomial is monic. -/
theorem rationalPrimeChangedIntegralPolynomial_monic (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    (rationalPrimeChangedIntegralPolynomial p hp n u).Monic := by
  letI : Fact p.Prime := ⟨hp⟩
  exact primeChangedPrimitivePolynomial_monic p (u.val * p) n

/-- Its exact degree is the required primitive prime-power degree. -/
theorem rationalPrimeChangedIntegralPolynomial_natDegree (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    (rationalPrimeChangedIntegralPolynomial p hp n u).natDegree = (p - 1) * p ^ n := by
  letI : Fact p.Prime := ⟨hp⟩
  exact primeChangedPrimitivePolynomial_natDegree p (u.val * p) n

/-- Its constant coefficient is the literal original unit times prime. -/
theorem rationalPrimeChangedIntegralPolynomial_coeff_zero (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    (rationalPrimeChangedIntegralPolynomial p hp n u).coeff 0 = u.val * p := by
  letI : Fact p.Prime := ⟨hp⟩
  exact primeChangedPrimitivePolynomial_coeff_zero p (u.val * p) n

/-- The actual changed integral polynomial is Eisenstein at its displayed uniformizer. -/
theorem rationalPrimeChangedIntegralPolynomial_isEisensteinAt (p : ℕ) (hp : p.Prime)
    (n : ℕ) (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    (rationalPrimeChangedIntegralPolynomial p hp n u).IsEisensteinAt
      (Ideal.span {u.val * p}) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact primeChangedPrimitivePolynomial_isEisensteinAt p (u.val * p)
    (rationalPrimeChangedIntegralUniformizer_prime p hp u) n

/-- Eisenstein makes the actual changed integral root algebra a domain. -/
local instance rationalPrimeChangedIntegralRootDomain (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    IsDomain (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u)) :=
  by
    letI : Fact p.Prime := ⟨hp⟩
    exact AdjoinRoot.isDomain_of_prime
      (primeChangedPrimitivePolynomial_irreducible p (u.val * p)
        (rationalPrimeChangedIntegralUniformizer_prime p hp u) n).prime

/-- The actual changed integral root algebra is a genuine DVR. -/
local instance rationalPrimeChangedIntegralRootDVR (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    IsDiscreteValuationRing (AdjoinRoot (rationalPrimeChangedIntegralPolynomial p hp n u)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply monic_eisenstein_adjoinRoot_dvr _
    (rationalPrimeChangedIntegralPolynomial_monic p hp n u) _ (u.val * p)
    (rationalPrimeChangedIntegralUniformizer_prime p hp u)
    (rationalPrimeChangedIntegralPolynomial_coeff_zero p hp n u)
    (rationalPrimeChangedIntegralPolynomial_isEisensteinAt p hp n u)
  rw [rationalPrimeChangedIntegralPolynomial_natDegree]
  exact Nat.mul_pos (Nat.sub_pos_of_lt hp.one_lt) (pow_pos hp.pos n)

/-- Its literal adjoined root is a genuine uniformizer. -/
theorem rationalPrimeChangedIntegralRoot_irreducible (p : ℕ) (hp : p.Prime) (n : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) :
    Irreducible (AdjoinRoot.root (rationalPrimeChangedIntegralPolynomial p hp n u)) := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  symm
  exact IsLocalRing.eq_maximalIdeal (prime_constant_adjoinRoot_root_maximal _
    (u.val * p) (rationalPrimeChangedIntegralUniformizer_prime p hp u)
    (rationalPrimeChangedIntegralPolynomial_coeff_zero p hp n u))

end
end Dubon2026
