import Dubon2026.AdelicLocalSphericalTrace
import Dubon2026.PrimitiveEulerFactors

/-! # Original local Euler series from the intrinsic spherical fixed-line trace

The polynomial is built from the actual local operator. Its Euler interpretation
is proved at good primes below. Identification of the entire abstract Satake
transform is a separate statement.
-/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Polynomial

/-- The determinant-one quadratic built from the actual original spherical Hecke trace. -/
def adelicLocalHeckeEulerPolynomial {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime]
    {k : ℤ} (F : PrimitiveCuspForm N k) : ℂ[X] :=
  1 - C (finitePlaceNormalizedSphericalTrace p
    (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) * X + X ^ 2

/-- At a good prime, the intrinsic original spherical Hecke polynomial is the exact original Fourier Euler polynomial. -/
theorem adelicLocalHeckeEulerPolynomial_eq_fourier {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime]
    {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    adelicLocalHeckeEulerPolynomial (p := p) F = 1 - C (normalizedCuspCoefficients F.toCuspForm p) * X + X ^ 2 := by
  unfold adelicLocalHeckeEulerPolynomial
  rw [adelicLocalNormalizedSphericalTrace_eq_fourier F hpN]

/-- The convergent original local Fourier Dirichlet series is the inverse evaluation of the polynomial built from the actual local fixed-line Hecke trace. -/
theorem primitive_good_euler_series_intrinsic_trace {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime]
    {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 ≤ k) (hpN : p.Coprime N)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' r : ℕ, primitiveLocalTerm F p s r) =
      ((adelicLocalHeckeEulerPolynomial (p := p) F).eval ((p : ℂ) ^ (-s)))⁻¹ := by
  have hp := (Fact.out : p.Prime)
  rw [adelicLocalHeckeEulerPolynomial_eq_fourier F hpN]
  simp only [eval_add, eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_pow]
  exact primitive_good_euler_series F hk hp ((hp.coprime_iff_not_dvd).mp hpN) hs

end
end Dubon2026
