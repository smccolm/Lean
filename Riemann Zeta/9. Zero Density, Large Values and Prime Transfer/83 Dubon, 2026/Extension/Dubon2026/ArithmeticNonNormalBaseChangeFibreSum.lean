import Dubon2026.ArithmeticNonNormalBaseChangePrimeCoordinate
import Dubon2026.OriginalPrimeFibreInvariantDegreeInOverfield

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

/-- Sum the actual canonical target coordinates over one original
prime fibre through the possibly nonnormal intermediate field. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_fibre_sum_in_galois_overfield
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    (∑ᶠ u : OriginalPrimeFibre K E v,
      rationalArithmeticRelativeStageIdelePrimeInvariant a E M hEM u.val
        (rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x)) =
      Module.finrank K E • rationalArithmeticRelativeStageIdelePrimeInvariant a K L hKL v x := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := ((IntermediateField.inclusion (hKE.trans hEM)).toAlgebra).toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (IntermediateField.inclusion (hKE.trans hEM))
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  letI : IsGalois K M := hGalKM
  let y := rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x
  calc
    _ = ∑ᶠ u : OriginalPrimeFibre K E v,
        originalPrimeFibreCompletionDegree K E v u •
          rationalArithmeticRelativeStageIdelePrimeInvariant a K L hKL v x := by
      apply finsum_congr
      intro u
      have hc := rationalArithmeticRelativeStageIdeleBaseChange_prime_coordinate_in_galois_overfield
        a K E L M hKE hKL hEM hLM x u.val
      have hd := originalPrimeFibreCompletionDegree_at_contraction K E v u
      rw [← hd, u.property] at hc
      exact hc
    _ = Module.finrank K E • rationalArithmeticRelativeStageIdelePrimeInvariant a K L hKL v x :=
      originalPrimeFibre_invariant_degree_in_galois_overfield K E M v _

end
end Dubon2026
