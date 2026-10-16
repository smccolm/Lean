import Dubon2026.OriginalLocalTraceTotalFormula
import Dubon2026.ArithmeticRelativeIdelePrimeOrbitSupport

/-! # The actual canonical total of every original local trace

The genuine trace lift is supported over its one contracted base prime.
The canonical total therefore equals that prime coordinate for every local
class, without a normalization hypothesis. This is the comparison needed
for DUB-17's arbitrary supplied local fundamental-class images.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

/-- Every actual original local class has canonical trace total equal to its canonical base-prime coordinate, by the proved support over that base prime. -/
theorem rationalArithmeticRelativeStage_local_trace_total
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H] :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalTraceTotalFormula F H
      (fun w => rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
        (originalFinitePrimeBelow F H w))
      (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  change OriginalLocalTraceTotalFormula F H
    (fun w => rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
      (originalFinitePrimeBelow F H w))
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
  intro w
  letI : Fintype Gal(H/F) := AlgEquiv.fintype F H
  letI : Finite (Gal(H/F) ⧸ OriginalFiniteDecompositionGroup F H w) :=
    @Quotient.finite (Gal(H/F)) (@Fintype.finite _ (AlgEquiv.fintype F H))
      (QuotientGroup.leftRel (OriginalFiniteDecompositionGroup F H w))
  letI : Fintype (Gal(H/F) ⧸ OriginalFiniteDecompositionGroup F H w) := Fintype.ofFinite _
  change ∀ y : groupCohomology (originalAdicUnitRep F H w) 2,
    rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH
      (originalSinglePrimeIdeleH2Lift F H w y) =
    rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH (originalFinitePrimeBelow F H w)
      (originalSinglePrimeIdeleH2Lift F H w y)
  intro y
  have hs : ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
      originalFinitePrimeBelow F H t ≠ originalFinitePrimeBelow F H w →
      originalFullIdeleAdicH2 F H t (originalSinglePrimeIdeleH2Lift F H w y) = 0 :=
    fun t ht => originalSinglePrimeIdeleH2Lift_other_base F H w t ht y
  have hz : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      v ≠ originalFinitePrimeBelow F H w →
        rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH v
          (originalSinglePrimeIdeleH2Lift F H w y) = 0 :=
    fun v hv => rationalArithmeticRelativeStageIdelePrimeInvariant_base_support a F H hFH w _ hs v hv
  exact (rationalArithmeticRelativeStageIdeleTotalInvariant_apply a F H hFH
    (originalSinglePrimeIdeleH2Lift F H w y)).trans
      (finsum_eq_single _ (originalFinitePrimeBelow F H w) hz)

end
end Dubon2026
