import Dubon2026.OriginalIdeleInfinitePrincipalKernel
import Dubon2026.ArithmeticRelativePrimePowerPrincipalKernel
import Dubon2026.ArithmeticRelativeStageClassProjection

/-! # Actual class-kernel reciprocity for every allowed positive prime power

The genuine degree and original real comparison discharge principal
reciprocity. Sequence exactness then kills finite total on the actual
zero-infinite class kernel without cyclicity. This supplies DUB-17's
general-stage auxiliary normalization comparison.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

variable (a : 𝓞 ℚ)
  (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]

/-- Zero original class projection and zero infinite localizations force
zero finite total at every actual allowed positive prime-power stage. -/
theorem rationalArithmeticRelativeStage_total_zero_of_class_zero_of_infinite
    (q r : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ (r + 1)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    ∀ x : rationalArithmeticRelativeStageIdeleH2 a K E hKE,
      (∀ v : NumberField.InfinitePlace E, originalFullIdeleInfiniteH2 K E v x = 0) →
      rationalArithmeticRelativeStageClassProjection a K E hKE x = 0 →
      rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE x = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  exact originalFullIdele_total_zero_of_class_zero_of_infinite K E
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE)
    (rationalArithmeticRelativeStageIdeleTotalInvariant_principal_of_infinite
      a K E hKE q r hq hqa hdegree)

end
end Dubon2026
