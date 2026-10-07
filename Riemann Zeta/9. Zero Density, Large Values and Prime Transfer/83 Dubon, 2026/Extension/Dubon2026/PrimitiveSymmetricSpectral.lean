import Dubon2026.LocalSpectralLogDerivative
import Dubon2026.PrimitiveCharacterBoundary

/-! # Actual unramified symmetric-power spectral factors of primitive cusp forms

The finite primes dividing the level are explicitly omitted: their local
factor is one. All unramified factors use the constructed actual Hecke roots.
-/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual symmetric-power spectral eigenvalues for the Euler product with ramified primes omitted. -/
def primitiveSymmetricSpectralRoots {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (i : Fin (r + 1)) : ℂ :=
  if (p : ℕ) ∣ Q then 0 else
    primitiveSatakePlus f p ^ (i : ℕ) * primitiveSatakeMinus f p ^ (r - (i : ℕ))

/-- The explicit prime bound supplies norm at most one for every genuine unramified symmetric-power eigenvalue. -/
theorem norm_primitiveSymmetricSpectralRoots_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) (p : Nat.Primes) (i : Fin (r + 1)) : ‖primitiveSymmetricSpectralRoots f r p i‖ ≤ 1 := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, if_pos hpQ, norm_zero, zero_le_one]
  · obtain ⟨hα,hβ⟩ := (primitiveSatake_unit_iff_bound f p.property hpQ).mpr (hbound p p.property hpQ)
    simp only [primitiveSymmetricSpectralRoots, if_neg hpQ, norm_mul, norm_pow,
      hα, hβ, one_pow, mul_one, le_refl]

/-- The complete spectral trace is the actual real prime character, with the same finite ramified set removed. -/
theorem primitiveSymmetricSpectralRoots_trace {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) :
    (∑ i : Fin (r + 1), primitiveSymmetricSpectralRoots f r p i) =
      (primitivePrimeCharacter f r p : ℂ) := by
  by_cases hpQ : (p : ℕ) ∣ Q
  · simp only [primitiveSymmetricSpectralRoots, primitivePrimeCharacter, if_pos hpQ,
      Finset.sum_const_zero, Complex.ofReal_zero]
  · simp only [primitiveSymmetricSpectralRoots, primitivePrimeCharacter, if_neg hpQ]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => primitiveSatakePlus f p ^ i *
      primitiveSatakeMinus f p ^ (r - i)) (r + 1)]
    change satakeSymmetricTrace (primitiveSatakePlus f p) (primitiveSatakeMinus f p) r = _
    rw [← primitive_primePower_eq_satakeTrace f p.property hpQ]
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      exact primitiveCuspForm_normalizedCoefficient_im f _
        ((p.property.coprime_iff_not_dvd.mpr hpQ).pow_left r)

/-- The unramified local spectral product is exactly the reciprocal of the actual symmetric-power Euler polynomial. -/
theorem primitiveSymmetricSpectralEulerFactor_good {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (hpQ : ¬(p : ℕ) ∣ Q) (s : ℂ) :
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p s =
      ((primitiveSymmetricEulerPolynomial f p r).eval (((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  simp only [primeSpectralEulerFactor, primitiveSymmetricSpectralRoots, if_neg hpQ,
    primitiveSymmetricEulerPolynomial, symmetricEulerPolynomial_eval]
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => 1 - primitiveSatakePlus f p ^ i *
    primitiveSatakeMinus f p ^ (r - i) * (((p : ℕ) : ℂ) ^ (-s))) (r + 1)]

/-- Omitting a ramified prime means exactly that its factor is one in the incomplete Euler product. -/
theorem primitiveSymmetricSpectralEulerFactor_bad {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (hpQ : (p : ℕ) ∣ Q) (s : ℂ) :
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots f r) p s = 1 := by
  simp only [primeSpectralEulerFactor, primitiveSymmetricSpectralRoots, if_pos hpQ,
    zero_mul, sub_zero, Finset.prod_const_one, inv_one]

/-- The literal first-prime spectral term equals the original prime-character logarithmic Dirichlet summand. -/
theorem primitiveSymmetricSpectralFirstTerm_eq {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r : ℕ) (p : Nat.Primes) (s : ℂ) :
    primeSpectralFirstTerm (primitiveSymmetricSpectralRoots f r) p s =
      (primeLogCoefficients (primitivePrimeCharacter f r) p : ℂ) * (((p : ℕ) : ℂ) ^ (-s)) := by
  rw [primeSpectralFirstTerm, primitiveSymmetricSpectralRoots_trace,
    primeLogCoefficients, if_pos p.property, Complex.ofReal_mul]
  ring

/-- The actual primitive higher-prime-power remainder is holomorphic on Re(s)>1/2 under the explicit local coefficient bound. -/
theorem primitiveSymmetricSpectralTail_analyticOnNhd {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) :
    AnalyticOnNhd ℂ (primeSpectralTail (primitiveSymmetricSpectralRoots f r)) {s : ℂ | 1 / 2 < s.re} :=
  primeSpectralTail_analyticOnNhd (norm_primitiveSymmetricSpectralRoots_le f hbound r)

end
end Dubon2026
