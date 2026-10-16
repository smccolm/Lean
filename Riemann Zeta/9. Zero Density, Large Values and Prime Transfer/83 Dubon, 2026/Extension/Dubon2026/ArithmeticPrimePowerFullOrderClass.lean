import Dubon2026.ArithmeticPrimePowerClassGenerator
import Dubon2026.OriginalClassFullOrderFromSpan

/-! # A constructed full-order class at every actual odd-primary stage

Retain the full order of the generator obtained from the constructed
auxiliary fields. This removes the arithmetic full-order-witness input
of the existing normalized subgroup-invariant construction for DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup

/-- Every actual finite Galois odd-prime-power stage in the fixed arithmetic union has a constructed original class of full extension-degree order. -/
theorem rationalArithmeticRelativePrimePower_exists_full_order_class
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = Module.finrank K E := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  obtain ⟨y, hc, hs⟩ := rationalArithmeticRelativePrimePower_exists_class_generator
    a K E hKE q t hq hq2 hqa hdegreeKE
  exact ⟨y, originalIdeleClass_full_order_of_span K E y hc hs⟩

end
end Dubon2026
