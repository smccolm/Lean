import Dubon2026.ArithmeticRelativeStageIdeleOrbitInvariant

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)
  [hGal : letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    IsGalois F H]

/-- Every actual full-idele H2 class at the finite stage has a finite set of genuine lower primes supporting each normalized completion coordinate. -/
theorem rationalArithmeticRelativeStageIdeleOrbitInvariant_exists_support
    (x : rationalArithmeticRelativeStageIdeleH2 a F H hFH) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)),
      ∀ (p : ℕ) (hp : p.Prime)
        (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F),
      rationalArithmeticOrbitPrime a p hp F c ∉ T →
        rationalArithmeticRelativeStageIdeleOrbitInvariant a p hp F H hFH c x = 0 := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : Module F H := Algebra.toModule
  letI : SMul F H := ((IntermediateField.inclusion hFH).toAlgebra).toSMul
  letI : IsScalarTower ℚ F H := IsScalarTower.of_algHom (IntermediateField.inclusion hFH)
  letI : FiniteDimensional F H := FiniteDimensional.right ℚ F H
  letI : IsGalois F H := hGal
  classical
  obtain ⟨S, hS⟩ := originalFullIdeleAdicH2_exists_finite_support F H x
  refine ⟨S.image (originalFinitePrimeBelow F H), ?_⟩
  intro p hp c hc
  have hbelow : originalFinitePrimeBelow F H
      (rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out)) =
      rationalArithmeticOrbitPrime a p hp F c := by
    simpa only [rationalArithmeticOrbitCoset_project_out a F H hFH c] using
      rationalArithmeticOrbitPrime_under a p hp F H hFH (QuotientGroup.mk c.out)
  have hout : rationalArithmeticOrbitPrime a p hp H (QuotientGroup.mk c.out) ∉ S := by
    intro hw
    exact hc (Finset.mem_image.mpr ⟨_, hw, hbelow⟩)
  exact rationalArithmeticRelativeStageIdeleOrbitInvariant_eq_zero_of_adic a p hp F H hFH c x (hS _ hout)

end
end Dubon2026
