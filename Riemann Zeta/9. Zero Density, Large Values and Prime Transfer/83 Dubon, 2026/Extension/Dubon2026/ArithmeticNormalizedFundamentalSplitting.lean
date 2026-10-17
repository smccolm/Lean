import Dubon2026.OriginalNormalizedQuotientSplitting
import Dubon2026.ArithmeticPrimePowerNormalizedQuotientSystem

/-! # The actual arithmetic normalized fundamental coefficient

The existing source-normalized arithmetic quotient class system supplies
all hypotheses of the constructed fundamental extension. The actual stage
degree supplies its p-group property. This discharges the fundamental
coefficient's subgroup and positive/degree-zero vanishing on DUB-17's
finite class/Ext route; lattice-Hom duality and norm divisibility remain.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- The actual arithmetic odd-primary stage constructs the source-normalized fundamental splitting coefficient of its original outside-unit quotient, deriving subgroup H1/H2 vanishing, positive vanishing and literal invariant norm preimages without a class-system or acyclicity input. -/
theorem rationalArithmeticRelativePrimePower_normalized_fundamental_splitting
    (a : 𝓞 ℚ) (ha : a ≠ 0) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    letI : IsGalois F H := hGal
    OriginalNormalizedQuotientSplitting F H
      (originalExceptionalIntegerSupport H (algebraMap (𝓞 ℚ) (𝓞 H) a)
        (originalIntegerMap_ne_zero (L := H) a ha))
      (rationalArithmeticIntermediateRelativeClassSupport_stable a ha F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  letI : Fact q.Prime := ⟨hq⟩
  have hG : IsPGroup q Gal(H/F) :=
    IsPGroup.of_card ((IsGalois.card_aut_eq_finrank F H).trans hdegree)
  exact originalClassQuotient_normalized_fundamental_splitting F H _ _ q hG
    (rationalArithmeticRelativePrimePower_normalized_quotient_system
      (hGal := hGal) a ha F H hFH q t hq hq2 hqa hdegree)

end
end Dubon2026
