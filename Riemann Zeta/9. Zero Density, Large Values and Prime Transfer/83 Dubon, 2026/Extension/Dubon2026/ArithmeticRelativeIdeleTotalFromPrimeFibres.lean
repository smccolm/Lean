import Dubon2026.ArithmeticNonNormalBaseChangeFibreSum
import Dubon2026.OriginalPrimeFibreFinsum
import Dubon2026.ArithmeticRelativeStageIdeleTotalInvariant

namespace Dubon2026
noncomputable section
open scoped NumberField Classical
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (K E M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hEM : E ≤ M)
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]
  [hGalEM : letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    IsGalois E M]

/-- The actual canonical totals satisfy the prescribed scalar relation once
the original prime fibres do. Finite support is derived for both genuine
idele classes. The base-change application supplies its proved fibre formula. -/
theorem rationalArithmeticRelativeStageIdeleTotalInvariant_eq_of_prime_fibres
    (x : rationalArithmeticRelativeStageIdeleH2 a K M (hKE.trans hEM))
    (y : rationalArithmeticRelativeStageIdeleH2 a E M hEM) (n : ℕ)
    (hfg : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        (∑ᶠ u : OriginalPrimeFibre K E v,
          rationalArithmeticRelativeStageIdelePrimeInvariant a E M hEM u.val
            y) =
          n • rationalArithmeticRelativeStageIdelePrimeInvariant a K M (hKE.trans hEM) v x) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    rationalArithmeticRelativeStageIdeleTotalInvariant a E M hEM
      y =
      n • rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM) x := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  have hy := rationalArithmeticRelativeStageIdelePrimeInvariant_hasFiniteSupport a E M hEM y
  have hx := rationalArithmeticRelativeStageIdelePrimeInvariant_hasFiniteSupport a K M (hKE.trans hEM) x
  exact originalPrimeFibre_finsum_eq_nsmul K E (n)
        (fun v => rationalArithmeticRelativeStageIdelePrimeInvariant a K M (hKE.trans hEM) v x)
        (fun u => rationalArithmeticRelativeStageIdelePrimeInvariant a E M hEM u y) hx hy hfg

end
end Dubon2026
