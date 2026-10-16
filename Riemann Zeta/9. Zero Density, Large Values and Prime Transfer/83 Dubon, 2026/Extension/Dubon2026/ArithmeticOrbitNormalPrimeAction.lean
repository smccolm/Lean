import Dubon2026.ArithmeticOrbitNormalField
import Dubon2026.ArithmeticOrbitPrimeCompletion
import Dubon2026.OriginalLocalEmbeddingPrimeGaloisComparison

/-! # The original global action on the primes of a normal arithmetic stage

All cosets generate the same local field at a normal stage. The literal
global embedding records the restricted coset automorphism, so the proved
prime-transport comparison identifies the precise original Galois action.
This is needed before prime transitivity can prove DUB-17's surjectivity.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [Normal ℚ F]
  (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)

/-- Identify the normal stage's two equal actual local intermediate fields. -/
def rationalArithmeticOrbitNormalFieldEquiv :
    rationalArithmeticOrbitLocalField a p hp F c ≃ₐ[rationalPrimeLocalField p hp]
      rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk 1) :=
  IntermediateField.equivOfEq (rationalArithmeticOrbitLocalField_eq_of_normal a p hp F c (QuotientGroup.mk 1))

/-- The original global generator changes by exactly the restricted coset automorphism. -/
theorem rationalArithmeticOrbitNormalFieldEquiv_global (x : F) :
    rationalArithmeticOrbitNormalFieldEquiv a p hp F c
      (rationalArithmeticOrbitFieldInclusion a p hp F c x) =
    rationalArithmeticOrbitFieldInclusion a p hp F (QuotientGroup.mk 1)
      ((rationalArithmeticOrbitRepresentative a F c).restrictNormal F x) := by
  apply Subtype.ext
  change rationalArithmeticOrbitEmbedding a p hp F c (x : rationalUnramifiedExtension a) =
    rationalArithmeticOrbitEmbedding a p hp F (QuotientGroup.mk 1)
      ((rationalArithmeticOrbitRepresentative a F c).restrictNormal F x : rationalUnramifiedExtension a)
  rw [rationalArithmeticOrbitEmbedding_mk]
  exact congrArg (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a)
    ((rationalArithmeticOrbitRepresentative a F c).restrictNormal_commutes F x).symm

variable [FiniteDimensional ℚ F]

/-- The exact restricted coset automorphism transports its induced original prime to the base induced prime. -/
theorem rationalArithmeticOrbitPrime_normal_action :
    numberFieldGaloisPlaceEquiv ℚ F ((rationalArithmeticOrbitRepresentative a F c).restrictNormal F)
      (rationalArithmeticOrbitPrime a p hp F c) =
        rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk 1) :=
  originalLocalEmbeddingPrime_galoisComparison F
    (rationalArithmeticOrbitLocalField a p hp F c)
    (rationalArithmeticOrbitLocalField a p hp F (QuotientGroup.mk 1)) p hp
    (rationalArithmeticOrbitNormalFieldEquiv a p hp F c).toAlgHom
    ((rationalArithmeticOrbitRepresentative a F c).restrictNormal F)
    (rationalArithmeticOrbitNormalFieldEquiv_global a p hp F c)

end
end Dubon2026
