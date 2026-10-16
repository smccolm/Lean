import Dubon2026.ArithmeticOrbitCommonRepresentativeTowers
import Dubon2026.ArithmeticOrbitNormalField

/-! # Actual completion degree selected by one arithmetic representative

Name the genuine completed field degree, with its original inclusion,
for DUB-17's arithmetic auxiliary-class local base-change formula.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
  (σ : rationalArithmeticGaloisGroup a)

/-- The actual local extension degree for the original completed field inclusion at the primes selected by the same arithmetic representative. -/
def rationalArithmeticOrbitCommonPrimeDegree : ℕ := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K E hKE σ
  letI : Algebra (rationalArithmeticOrbitPrimeCompletion a p hp K (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrimeCompletion a p hp E (QuotientGroup.mk σ)) :=
    (originalAdicBaseChangeMap K E (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ))).toAlgebra
  letI : Module (rationalArithmeticOrbitPrimeCompletion a p hp K (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrimeCompletion a p hp E (QuotientGroup.mk σ)) := Algebra.toModule
  exact Module.finrank (rationalArithmeticOrbitPrimeCompletion a p hp K (QuotientGroup.mk σ))
    (rationalArithmeticOrbitPrimeCompletion a p hp E (QuotientGroup.mk σ))

end
end Dubon2026
