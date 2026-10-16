import Dubon2026.ArithmeticOrbitCompletionGlobalTowers
import Dubon2026.OriginalLocalCompletionEquivContinuity
import Dubon2026.RationalPrimeContinuousScalarMap
import Dubon2026.OriginalEqualPrimeCompletionComparison

/-! # Equal original primes give a literal local-field comparison

The original completed identity compares the orbit fields of two arithmetic
cosets inducing the same prime. Rational density makes it linear over the
original rational-prime completion. This supplies the injectivity input
for DUB-17's indexing of local Mackey orbits by original finite primes.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitCompletionBaseAlgebra
  arithmeticOrbitCompletionValuation arithmeticOrbitCompletionTopology arithmeticOrbitCompletionLocalField
  arithmeticOrbitCompletionValuationExtension arithmeticOrbitCompletionUniformity arithmeticOrbitCompletionUniformAdd
  arithmeticOrbitCompletionGlobalAlgebra arithmeticOrbitCompletionGlobalSmul arithmeticOrbitCompletionOrbitSmul

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (c c' : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
  (h : rationalArithmeticOrbitPrime a p hp F c = rationalArithmeticOrbitPrime a p hp F c')

/-- Transport the original completed identity between the two equal induced primes. -/
def rationalArithmeticOrbitEqualPrimeRingEquiv :
    rationalArithmeticOrbitLocalField a p hp F c ≃+* rationalArithmeticOrbitLocalField a p hp F c' :=
  originalEqualPrimeCompletionComparison F
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c')
    (rationalArithmeticOrbitPrime a p hp F c) (rationalArithmeticOrbitPrime a p hp F c') h
    (rationalArithmeticOrbitCompletionEquiv a p hp F c) (rationalArithmeticOrbitCompletionEquiv a p hp F c')

/-- The completed comparison preserves the original local topologies. -/
theorem rationalArithmeticOrbitEqualPrimeRingEquiv_continuous :
    Continuous (rationalArithmeticOrbitEqualPrimeRingEquiv a p hp F c c' h) :=
  originalEqualPrimeCompletionComparison_continuous F
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c')
    (rationalArithmeticOrbitPrime a p hp F c) (rationalArithmeticOrbitPrime a p hp F c') h
    (rationalArithmeticOrbitCompletionEquiv a p hp F c) (rationalArithmeticOrbitCompletionEquiv a p hp F c')
    (originalLocalCompletionEquiv_symm_continuous F (rationalArithmeticOrbitLocalField a p hp F c) p hp
      (rationalArithmeticOrbitField_ranges a p hp F c))
    (originalLocalCompletionEquiv_continuous F (rationalArithmeticOrbitLocalField a p hp F c') p hp
      (rationalArithmeticOrbitField_ranges a p hp F c'))

/-- The comparison fixes the entire original rational-prime completion. -/
def rationalArithmeticOrbitEqualPrimeAlgEquiv :
    rationalArithmeticOrbitLocalField a p hp F c ≃ₐ[rationalPrimeLocalField p hp]
      rationalArithmeticOrbitLocalField a p hp F c' where
  __ := rationalArithmeticOrbitEqualPrimeRingEquiv a p hp F c c' h
  commutes' x := rationalPrimeLocal_continuousRingHom_commutes p hp
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c')
    (rationalArithmeticOrbitEqualPrimeRingEquiv a p hp F c c' h).toRingHom
    (rationalArithmeticOrbitEqualPrimeRingEquiv_continuous a p hp F c c' h) x

/-- The comparison identifies the two literal embeddings of the original global field. -/
theorem rationalArithmeticOrbitEqualPrimeAlgEquiv_global (x : F) :
    rationalArithmeticOrbitEqualPrimeAlgEquiv a p hp F c c' h
      (rationalArithmeticOrbitFieldInclusion a p hp F c x) =
        rationalArithmeticOrbitFieldInclusion a p hp F c' x := by
  have he := originalEqualPrimeCompletionComparison_algebraMap F
    (rationalArithmeticOrbitLocalField a p hp F c) (rationalArithmeticOrbitLocalField a p hp F c')
    (rationalArithmeticOrbitPrime a p hp F c) (rationalArithmeticOrbitPrime a p hp F c') h
    (rationalArithmeticOrbitCompletionEquiv a p hp F c) (rationalArithmeticOrbitCompletionEquiv a p hp F c') x
  exact (congrArg (rationalArithmeticOrbitEqualPrimeRingEquiv a p hp F c c' h)
    (rationalArithmeticOrbitCompletionEquiv_algebraMap a p hp F c x).symm).trans
      (he.trans (rationalArithmeticOrbitCompletionEquiv_algebraMap a p hp F c' x))

end
end Dubon2026
