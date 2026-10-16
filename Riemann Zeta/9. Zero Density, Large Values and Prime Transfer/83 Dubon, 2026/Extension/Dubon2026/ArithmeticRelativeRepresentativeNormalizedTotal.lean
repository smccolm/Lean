import Dubon2026.ArithmeticRelativeRepresentativeNormalizedLift
import Dubon2026.ArithmeticRelativePrimeInvariantRepresentative
import Dubon2026.ArithmeticRelativeNormalizedPrimeTotal

/-! # Joint local and total normalization at every representative

Retain the same original local class while using prime-choice independence
to identify its prime coordinate. Its genuine trace is supported over the
one base prime, so the canonical total has the same normalized value.
This removes DUB-17's restriction to the canonical upper representative.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F H : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [FiniteDimensional ℚ H] (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Every actual arithmetic representative has one original local class normalizing both its canonical base-prime coordinate and the canonical total to the reciprocal decomposition degree. -/
theorem rationalArithmeticRelativeStage_exists_representative_normalized_trace
    (p : ℕ) (hp : p.Prime) (σ : rationalArithmeticGaloisGroup a) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : Module F H := Algebra.toModule
    letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
    letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
    letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
    OriginalLocalTraceJointNormalization F H
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ))
      (rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH
        (rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)))
      (rationalArithmeticRelativeStageIdeleTotalInvariant a F H hFH) := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  let v := rationalArithmeticOrbitPrime a p hp F (QuotientGroup.mk σ)
  let w := rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk σ)
  letI := rationalArithmeticOrbitPrime_commonRepresentative_liesOver a p hp F H hFH σ
  letI : Fintype Gal(H/F) := AlgEquiv.fintype F H
  letI : Finite (Gal(H/F) ⧸ OriginalFiniteDecompositionGroup F H w) :=
    @Quotient.finite (Gal(H/F)) (@Fintype.finite _ (AlgEquiv.fintype F H))
      (QuotientGroup.leftRel (OriginalFiniteDecompositionGroup F H w))
  letI : Fintype (Gal(H/F) ⧸ OriginalFiniteDecompositionGroup F H w) := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := rationalArithmeticRelativeStage_exists_representative_normalized_local_trace
    (hGal := hGal) a p hp F H hFH σ
  have hb : originalFinitePrimeBelow F H w = v :=
    originalFinitePrimeBelow_eq_of_liesOver F H v w
  have hi := (rationalArithmeticRelativeStageIdelePrimeInvariant_eq_representative
    a F H hFH p hp σ (originalSinglePrimeIdeleH2Lift F H w y)).trans hy
  have hs : ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 H),
      originalFinitePrimeBelow F H t ≠ originalFinitePrimeBelow F H w →
      originalFullIdeleAdicH2 F H t (originalSinglePrimeIdeleH2Lift F H w y) = 0 :=
    fun t ht => originalSinglePrimeIdeleH2Lift_other_base F H w t ht y
  have hz : ∀ v' : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v' ≠ v →
      rationalArithmeticRelativeStageIdelePrimeInvariant a F H hFH v'
        (originalSinglePrimeIdeleH2Lift F H w y) = 0 := by
    intro v' hv'
    apply rationalArithmeticRelativeStageIdelePrimeInvariant_base_support a F H hFH w _ hs v'
    exact fun h => hv' (h.trans hb)
  refine ⟨y, hi, ?_⟩
  exact (rationalArithmeticRelativeStageIdeleTotalInvariant_apply a F H hFH
    (originalSinglePrimeIdeleH2Lift F H w y)).trans ((finsum_eq_single _ v hz).trans hi)

end
end Dubon2026
