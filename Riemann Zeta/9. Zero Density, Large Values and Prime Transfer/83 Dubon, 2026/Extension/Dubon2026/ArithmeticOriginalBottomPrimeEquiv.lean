import Dubon2026.ArithmeticCommonStageRationalTotal
import Dubon2026.OriginalFinitePrimeOrbits

/-! Reindex the actual canonical arithmetic bottom-field total by the
original rational number-field primes. The literal inclusion is retained;
the rational field and its bottom-field copy are not identified by fiat.
This is the indexing edge in DUB-17's rational canonical cup-total comparison. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ)

/-- The actual bottom-field integer inclusion is surjective, through the
existing rational bottom-field equivalence and its original integer map. -/
theorem arithmeticOriginalBottomIntegerMap_surjective :
    Function.Surjective (algebraMap (𝓞 ℚ)
      (𝓞 (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)))) := by
  let K : IntermediateField ℚ (rationalUnramifiedExtension a) := ⊥
  let e : ℚ ≃ₐ[ℚ] K := (IntermediateField.botEquiv ℚ (rationalUnramifiedExtension a)).symm
  have he : (NumberField.RingOfIntegers.mapAlgEquiv e).toRingHom =
      algebraMap (𝓞 ℚ) (𝓞 K) := by
    apply RingHom.ext
    intro x
    apply NumberField.RingOfIntegers.ext
    exact e.commutes x.val
  rw [← he]
  exact (NumberField.RingOfIntegers.mapAlgEquiv e).surjective

/-- Literal prime contraction from the arithmetic bottom field is
bijective, using surjectivity of its actual integer inclusion. -/
theorem arithmeticOriginalBottomPrimeBelow_bijective :
    Function.Bijective (originalFinitePrimeBelow ℚ
      (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) := by
  refine ⟨fun v w h => ?_, originalFinitePrimeBelow_surjective ℚ _⟩
  apply HeightOneSpectrum.ext
  exact Ideal.comap_injective_of_surjective _
    (arithmeticOriginalBottomIntegerMap_surjective a) (congrArg HeightOneSpectrum.asIdeal h)

/-- The canonical total's original bottom-field primes correspond
bijectively to the original rational number-field primes by contraction. -/
def arithmeticOriginalBottomPrimeEquiv :
    HeightOneSpectrum (𝓞 (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))) ≃
      HeightOneSpectrum (𝓞 ℚ) :=
  Equiv.ofBijective (originalFinitePrimeBelow ℚ _)
    (arithmeticOriginalBottomPrimeBelow_bijective a)

end
end Dubon2026
