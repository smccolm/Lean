import Dubon2026.ArithmeticFiniteStageIdeleOrbitInvariant

/-! # Individual original-prime support for the actual full-idele invariant

Contract the proved finite support of the original full-idele H2 class.
The literal prime contraction identifies each coordinate outside that
set, so its normalized invariant vanishes. This supplies finite support
for the full-idele total on DUB-17's class-invariant descent route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticFiniteStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- Every actual full-idele H2 class at the finite stage has a finite set of genuine lower primes supporting each normalized completion coordinate. -/
theorem rationalArithmeticFiniteStageIdeleOrbitInvariant_exists_support
    (x : rationalArithmeticFiniteStageIdeleH2 a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      ∀ (p : ℕ) (hp : p.Prime)
        (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F),
      rationalArithmeticOrbitPrime a p hp F c ∉ T →
        rationalArithmeticFiniteStageIdeleOrbitInvariant a p hp F H hFH c x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := IsGalois.tower_top_of_isGalois ℚ F H
  classical
  obtain ⟨S, hS⟩ := originalFullIdeleAdicH2_exists_finite_support F H x
  refine ⟨S.image (originalFinitePrimeBelow F H), ?_⟩
  intro p hp c hc
  have hbelow : originalFinitePrimeBelow F H
      (rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p hp F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H.toIntermediateField hFH c] using
      rationalArithmeticOrbitPrime_under a p hp F H.toIntermediateField hFH (QuotientGroup.mk c.out)
  have hout : rationalArithmeticOrbitPrime a p hp H.toIntermediateField (QuotientGroup.mk c.out) ∉ S := by
    intro hw
    exact hc (Finset.mem_image.mpr ⟨_, hw, hbelow⟩)
  exact rationalArithmeticFiniteStageIdeleOrbitInvariant_eq_zero_of_adic a p hp F H hFH c x (hS _ hout)

end
end Dubon2026
