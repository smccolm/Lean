import Dubon2026.ArithmeticPrimePowerCompletionRestrictions
import Dubon2026.OriginalFiniteNormalizedClassSystem

/-! # Source normalization for finite fields in the unrestricted union

The existing arithmetic constructor applies with exceptional integer
zero: its statement imposes divisibility by the odd prime but no
nonzero condition on that auxiliary integer. Restricting scalars turns
the actual extension over a finite base into its literal rational
arithmetic stage, with the same carrier and field inclusion. This
discharges normalization for the Kummer field needed by DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The original full-class system of a finite odd-primary extension in
the unrestricted arithmetic union is constructed with all source-normalized
completion restrictions. No normalized-system premise is supplied. -/
theorem originalUnrestricted_finite_normalized_class_system
    (F : IntermediateField ℚ (rationalUnramifiedExtension 0))
    [FiniteDimensional ℚ F]
    (N : IntermediateField F (rationalUnramifiedExtension 0))
    [FiniteDimensional F N] [NumberField N] [IsGalois F N]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (hdegree : Module.finrank F N = q ^ t) :
    OriginalFiniteNormalizedClassSystem F N := by
  let H := N.restrictScalars ℚ
  have hFH : F ≤ H := fun x hx => N.algebraMap_mem ⟨x, hx⟩
  letI : FiniteDimensional ℚ N := Module.Finite.trans F N
  letI : FiniteDimensional ℚ H := inferInstanceAs (FiniteDimensional ℚ N)
  have hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H := by
    change IsGalois F N
    infer_instance
  have hd : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t := hdegree
  exact originalIdeleClass_finite_normalized_system_of_completion_restrictions F N
    (rationalArithmeticRelativePrimePower_exists_completion_local_restrictions
      (hGal := hGal) 0 F H hFH q t hq hq2 (dvd_zero _) hd)

end
end Dubon2026
