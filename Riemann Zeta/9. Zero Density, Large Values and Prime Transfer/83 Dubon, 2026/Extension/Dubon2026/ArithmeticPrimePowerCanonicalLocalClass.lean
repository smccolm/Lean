import Dubon2026.OriginalCanonicalLocalClassNormalization
import Dubon2026.ArithmeticPrimePowerCanonicalTraceSystem

/-! # Construct normalized actual decomposition class invariants

For each original base prime in an odd-primary finite stage, combine the
constructed canonical class/trace system with the same local class that
normalizes both the local prime coordinate and the global prime total.
No class invariant, local witness or total-comparison certificate is an
input. Arbitrary upper-prime and inter-stage comparisons remain separate.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

/-- Every original base prime of an actual odd-primary Galois stage has an injective exact-image invariant on its canonical decomposition-subgroup class H2, normalized by the same constructed original local class as the completion invariant. -/
theorem rationalArithmeticRelativePrimePower_exists_canonical_local_class
    (a : 𝓞 ℚ) (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
    [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      IsGalois F H]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
      letI : Module F H := Algebra.toModule
      Module.finrank F H = q ^ t)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    let p := rationalArithmeticOriginalPrimeBase a F v
    let c := ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
      ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩).out
    OriginalCanonicalPrimeClassNormalization F H
      (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out))
      (rationalArithmeticRelativeStageIdeleOrbitInvariant a p.val p.property F H hFH c) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  let p := rationalArithmeticOriginalPrimeBase a F v
  let c := ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
    ⟨v, rationalArithmeticOriginalPrimeBase_below a F v⟩).out
  exact originalIdeleClass_canonical_prime_normalization F H
    (rationalArithmeticOrbitPrime a p.val p.property H (QuotientGroup.mk c.out))
    (rationalArithmeticRelativeStageIdeleOrbitInvariant a p.val p.property F H hFH c)
    (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH)
    (rationalArithmeticRelativePrimePower_exists_canonical_trace_system
      (hGalKE := hGal) a F H hFH q t hq hq2 hqa hdegree)
    (rationalArithmeticRelativeStage_exists_canonical_prime_normalized_trace
      (hGal := hGal) a F H hFH v)

end
end Dubon2026
