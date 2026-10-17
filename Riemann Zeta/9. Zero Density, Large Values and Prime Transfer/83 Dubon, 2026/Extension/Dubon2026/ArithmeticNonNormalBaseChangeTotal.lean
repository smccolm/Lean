import Dubon2026.ArithmeticNonNormalBaseChangeFibreSum
import Dubon2026.ArithmeticRelativeIdeleTotalFromPrimeFibres
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

/-- The canonical total of the actual restriction inside one Galois upper field is the
original total multiplied by the actual lower field degree, including the
nonnormal fixed field of the source obstruction's Sylow subgroup. -/
theorem rationalArithmeticRelativeStageIdeleBaseChange_total_in_galois_overfield
    (x : rationalArithmeticRelativeStageIdeleH2 a K M (hKE.trans hEM)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    rationalArithmeticRelativeStageIdeleTotalInvariant a E M hEM
      (rationalArithmeticRelativeStageIdeleBaseChange a K E M M hKE (hKE.trans hEM) hEM le_rfl x) =
      Module.finrank K E • rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM) x := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact rationalArithmeticRelativeStageIdeleTotalInvariant_eq_of_prime_fibres
    (hGalKM := hGalKM) (hGalEM := hGalEM) a K E M hKE hEM x
    (rationalArithmeticRelativeStageIdeleBaseChange a K E M M hKE (hKE.trans hEM) hEM le_rfl x)
    (Module.finrank K E)
    (fun v => rationalArithmeticRelativeStageIdeleBaseChange_fibre_sum_in_galois_overfield
      (hGalKM := hGalKM) (hGalKL := hGalKM) (hGalEM := hGalEM)
      a K E M M hKE (hKE.trans hEM) hEM le_rfl x v)

end
end Dubon2026
