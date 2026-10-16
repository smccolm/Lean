import Dubon2026.ArithmeticOrbitSubfieldTransport
import Dubon2026.OriginalLocalEmbeddingPrimeContraction

/-! # Actual arithmetic coset primes contract along the original finite cover

The literal generated-field inclusion preserves original global values.
Apply the proved valuation and maximal-ideal contraction comparison to
these actual objects. This is the descent step from the Galois-cover
surjectivity proof to DUB-17's arbitrary finite arithmetic field.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H)

/-- The upper arithmetic coset's genuine original prime contracts to the lower representative's genuine original prime. -/
theorem rationalArithmeticOrbitPrime_under :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    originalFinitePrimeBelow F H (rationalArithmeticOrbitPrime a p hp H c) =
      rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk c.out) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact originalLocalEmbeddingPrime_under_eq F H
    (rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk c.out))
    (rationalArithmeticOrbitLocalField a p hp H c) p hp
    (rationalArithmeticOrbitSubfieldMap a p hp F H hFH c)
    (rationalArithmeticOrbitSubfieldMap_global a p hp F H hFH c)

end
end Dubon2026
