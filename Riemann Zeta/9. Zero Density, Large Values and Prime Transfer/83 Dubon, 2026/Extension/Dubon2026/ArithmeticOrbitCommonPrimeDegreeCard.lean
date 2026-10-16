import Dubon2026.ArithmeticOrbitCommonPrimeDegree
import Dubon2026.OriginalAdicDecompositionDegree

/-! # The arithmetic local degree is the original prime stabilizer order

Reuse the proved original completion-degree theorem at the actual primes
selected by one arithmetic representative. This identifies DUB-17's
local base-change factor with the term in the proved prime-fibre sum.
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
  [hGal : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  (σ : rationalArithmeticGaloisGroup a)

/-- The actual completion degree in the arithmetic base-change formula is exactly the order of the original upper-prime decomposition group. -/
theorem rationalArithmeticOrbitCommonPrimeDegree_eq_decomposition_card :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    rationalArithmeticOrbitCommonPrimeDegree a p hp K E hKE σ =
      Nat.card (OriginalFiniteDecompositionGroup K E
        (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ))) := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGal
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K E hKE σ
  exact originalAdicBaseChange_finrank_eq_decomposition_card K E
    (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
    (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ))

end
end Dubon2026
