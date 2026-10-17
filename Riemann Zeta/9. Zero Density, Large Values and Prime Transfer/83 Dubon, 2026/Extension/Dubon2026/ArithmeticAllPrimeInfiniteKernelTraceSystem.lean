import Dubon2026.ArithmeticAllPrimeInfiniteKernelClassSystem
import Dubon2026.OriginalInfiniteKernelClassSystemTrace
import Dubon2026.ArithmeticAllPrimePowerFullOrderClass

/-! # Actual corestriction for canonically normalized arithmetic class invariants

Consume the constructed full-order class and the canonical invariant system
for the same actual stage. Native trace compatibility then applies to its
subgroup invariants, with no class, invariant or trace-identity hypothesis.
This supplies the corestriction input to DUB-17's local normalization step.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup

/-- Every actual finite Galois prime-power stage in the fixed arithmetic union has injective global and subgroup invariants with exact images, the literal idele-total formula on the zero-infinite domain and the subgroup-index relation, together with the genuine subgroup corestriction law and no supplied auxiliary fields or class witnesses. -/
theorem rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_trace_system
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
    letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
    letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
    OriginalInfiniteKernelClassInvariantTraceSystem K E
      (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGalKE
  exact originalIdeleClass_infinite_kernel_system_with_trace K E
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE)
    (rationalArithmeticRelativeAllPrimePower_exists_full_order_class
      (hGalKE := hGalKE) a K E hKE q t hq hqa hdegreeKE)
    (rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_class_system
      (hGalKE := hGalKE) a K E hKE q t hq hqa hdegreeKE)

end
end Dubon2026
