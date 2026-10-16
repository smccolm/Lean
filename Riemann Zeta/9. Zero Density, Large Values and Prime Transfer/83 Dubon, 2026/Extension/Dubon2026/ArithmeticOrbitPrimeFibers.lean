import Dubon2026.ArithmeticOrbitEqualPrimeLift
import Dubon2026.ArithmeticOrbitFieldTransport
import Dubon2026.OriginalLocalEmbeddingPrimeComparison

/-! # Original induced-prime fibers are precisely the actual local coset orbits

Both directions use the literal original embedding. A local Galois orbit
preserves the induced prime by the existing integer-ring equivalence;
equal original primes give a local Galois lift through their actual
completions. This discharges representative independence and injectivity
for DUB-17's prime indexing. Surjectivity and the total sum remain separate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- The original induced prime is unchanged on each actual local Galois orbit. -/
theorem rationalArithmeticOrbitPrime_eq_of_smul
    (d : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp))
    (h : rationalPrimeArithmeticRestriction a p hp d • c = c') :
    rationalArithmeticOrbitPrime a p hp F c = rationalArithmeticOrbitPrime a p hp F c' :=
  originalLocalEmbeddingPrime_eq_of_algEquiv F
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c') p hp
    (rationalArithmeticOrbitFieldTransport a p hp F c c' d h)
    (rationalArithmeticOrbitFieldTransport_global a p hp F c c' d h)

/-- Equality of genuine original primes is exactly equality of the actual local Galois orbit. -/
theorem rationalArithmeticOrbitPrime_eq_iff :
    rationalArithmeticOrbitPrime a p hp F c = rationalArithmeticOrbitPrime a p hp F c' ↔
      ∃ d : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp),
        rationalPrimeArithmeticRestriction a p hp d • c = c' := by
  constructor
  · intro h
    exact ⟨rationalArithmeticOrbitEqualPrimeLift a p hp F c c' h,
      rationalArithmeticOrbitEqualPrimeLift_smul a p hp F c c' h⟩
  · rintro ⟨d, h⟩
    exact rationalArithmeticOrbitPrime_eq_of_smul a p hp F c c' d h

end
end Dubon2026
