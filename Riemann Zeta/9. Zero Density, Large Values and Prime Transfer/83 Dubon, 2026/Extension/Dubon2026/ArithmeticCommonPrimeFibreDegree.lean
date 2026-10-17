import Dubon2026.ArithmeticOrbitCommonPrimeDegree
import Dubon2026.OriginalPrimeFibreDegreeAtContraction
import Dubon2026.OriginalFullIdeleInvariantPrimeSupport

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

/-- The arithmetic representative's local degree is exactly the actual
prime-fibre completion degree at the contraction of its upper prime.
No normality of the lower extension is used. -/
theorem rationalArithmeticOrbitCommonPrimeDegree_eq_fibre_degree :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    rationalArithmeticOrbitCommonPrimeDegree a p hp K E hKE σ =
      originalPrimeFibreCompletionDegree K E
        (originalFinitePrimeBelow K E (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ)))
        ⟨rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ), rfl⟩ := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K E hKE σ
  let v := rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ)
  let u := rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ)
  have hu : originalFinitePrimeBelow K E u = v := originalFinitePrimeBelow_eq_of_liesOver K E v u
  have hd : rationalArithmeticOrbitCommonPrimeDegree a p hp K E hKE σ =
      originalPrimeFibreCompletionDegree K E v ⟨u, hu⟩ := rfl
  exact hd.trans (originalPrimeFibreCompletionDegree_at_contraction K E v ⟨u, hu⟩)

end
end Dubon2026
