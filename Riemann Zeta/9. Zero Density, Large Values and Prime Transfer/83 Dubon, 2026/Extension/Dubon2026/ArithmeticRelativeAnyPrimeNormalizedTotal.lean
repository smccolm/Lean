import Dubon2026.ArithmeticRelativeRepresentativeNormalizedTotal
import Dubon2026.ArithmeticOrbitPrimeSurjectivity

/-! # Joint normalization at every actual upper prime

The proved arithmetic prime-surjectivity theorem represents an arbitrary
original prime. Transport the already constructed local class and both
normalization equations along that prime equality. No prime choice or
normalization certificate remains an input to DUB-17's finite-stage result.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- At every original upper prime, one constructed original local class normalizes both the canonical invariant of its contracted base prime and the canonical global total. -/
theorem rationalArithmeticRelativeStage_exists_any_prime_normalized_trace
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 H)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalTraceJointNormalization F H w
      (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH (originalFinitePrimeBelow F H w))
      (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  let p := rationalArithmeticOriginalPrimeBase a H w
  obtain ⟨c, hc⟩ := rationalArithmeticOrbitPrime_surjective a p.val p.property H w
    (rationalArithmeticOriginalPrimeBase_below a H w)
  have hrep : (QuotientGroup.mk c.out :
      rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a H) = c :=
    Quotient.out_eq' c
  have he : rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out) = w :=
    (congrArg (rationalArithmeticOrbitPrime a p.val p.property H) hrep).trans hc
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p.val p.property F H hFH c.out
  have hb := originalFinitePrimeBelow_eq_of_liesOver F H
    (rationalArithmeticOrbitPrime a p.val p.property F (QuotientGroup.mk c.out))
    (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out))
  have hn := rationalArithmeticRelativeStage_exists_representative_normalized_trace
    (hGal := hGal) a F H hFH p.val p.property c.out
  rw [← hb] at hn
  simpa only [he] using hn

end
end Dubon2026
