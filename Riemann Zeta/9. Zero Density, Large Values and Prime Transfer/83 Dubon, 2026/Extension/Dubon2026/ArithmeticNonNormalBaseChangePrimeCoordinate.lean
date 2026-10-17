import Dubon2026.ArithmeticNonNormalBaseChangeCommonInvariant
import Dubon2026.ArithmeticCommonPrimeFibreDegree
import Dubon2026.ArithmeticRelativePrimeInvariantRepresentative

namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]

/-- The actual canonical prime coordinate under base change through
the nonnormal intermediate field has the literal completion-degree factor.
The source prime is its actual contraction; no representative values or
choice-compatibility premise is supplied. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_prime_coordinate_in_galois_overfield
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (u : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    rationalArithmeticRelativeStageIdelePrimeInvariant a E M hEM u
      (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) =
      originalPrimeFibreCompletionDegree K E (originalFinitePrimeBelow K E u) ⟨u, rfl⟩ •
        rationalArithmeticRelativeStageIdelePrimeInvariant a K L hKL (originalFinitePrimeBelow K E u) x := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  obtain ⟨p, hp, σ, hu, hi⟩ :=
    rationalArithmeticRelativeStageIdelePrimeInvariant_exists_representative a E M hEM u
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp K E hKE σ
  have hv : rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ) =
      originalFinitePrimeBelow K E u :=
    (originalFinitePrimeBelow_eq_of_liesOver K E
      (rationalArithmeticOrbitPrime a p hp K (QuotientGroup.mk σ))
      (rationalArithmeticOrbitPrime a p hp E (QuotientGroup.mk σ))).symm.trans
        (congrArg (originalFinitePrimeBelow K E) hu)
  have hd := rationalArithmeticOrbitCommonPrimeDegree_eq_fibre_degree a p hp K E hKE σ
  have hs := rationalArithmeticRelativeStageIdelePrimeInvariant_eq_representative a K L hKL p hp σ x
  have hc := rationalArithmeticRelativeStageIdeleBaseChange_commonInvariant_in_galois_overfield
    a K E L M hKE hKL hEM hLM p hp σ x
  rw [hi, hc, ← hs, hd, hu, hv]

end
end Dubon2026
