import Dubon2026.ArithmeticRationalPrimeInvariant
import Dubon2026.ArithmeticOriginalBottomPrimeEquiv
import Dubon2026.OriginalPrimeTowerSelection
import Dubon2026.ArithmeticRelativePrimeCompletionComparison

/-! The actual rational canonical total indexed by original rational
number-field primes. The original bottom-field class and literal prime
contraction are retained. This supplies DUB-17's canonical total comparison
before the exceptional local Cartier family is substituted. -/
namespace Dubon2026
noncomputable section

private theorem addMonoidHom_apply_of_eq_comp
    {A B C : Type*} [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]
    (f : A →+ C) (g : B →+ C) (h : A →+ B)
    (he : f = g.comp h) (x : A) : f x = g (h x) :=
  congrArg (fun k : A →+ C => k x) he

open IsDedekindDomain
open scoped NumberField BigOperators
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  bottomInvariantStageAlgebra bottomInvariantStageModule bottomInvariantStageSMul
  bottomInvariantStageTower bottomInvariantStageRationalGalois bottomInvariantStageGalois
  bottomInvariantStageFinite

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The rational canonical total is definitionally the original relative
total of the actual bottom-field image; this identity introduces no normalization claim. -/
theorem arithmeticCommonStageRationalIdeleTotal_apply
    (x : groupCohomology (originalFullIdeleRep ℚ F) 2) :
    arithmeticCommonStageRationalIdeleTotal a F x =
      rationalArithmeticRelativeStageIdeleTotalInvariant (hGal := bottomInvariantStageGalois a F)
        a ⊥ F.toIntermediateField bot_le
        (arithmeticCommonStageIdeleToBottom a F x) := by
  exact addMonoidHom_apply_of_eq_comp (arithmeticCommonStageRationalIdeleTotal a F)
    (rationalArithmeticRelativeStageIdeleTotalInvariant
      (hGal := bottomInvariantStageGalois a F) a ⊥ F.toIntermediateField bot_le)
    (arithmeticCommonStageIdeleToBottom a F) (by rfl) x


/-- The canonical rational-prime coordinate is definitionally its
original bottom-field coordinate after the same actual idele map. -/
theorem arithmeticCommonStageRationalPrimeInvariant_apply
    (v : HeightOneSpectrum (𝓞 ℚ))
    (x : groupCohomology (originalFullIdeleRep ℚ F) 2) :
    arithmeticCommonStageRationalPrimeInvariant a F v x =
      rationalArithmeticRelativeStageIdelePrimeInvariant (hGal := bottomInvariantStageGalois a F)
        a ⊥ F.toIntermediateField bot_le ((arithmeticOriginalBottomPrimeEquiv a).symm v)
        (arithmeticCommonStageIdeleToBottom a F x) := by
  exact addMonoidHom_apply_of_eq_comp (arithmeticCommonStageRationalPrimeInvariant a F v)
    (rationalArithmeticRelativeStageIdelePrimeInvariant
      (hGal := bottomInvariantStageGalois a F) a ⊥ F.toIntermediateField bot_le
      ((arithmeticOriginalBottomPrimeEquiv a).symm v))
    (arithmeticCommonStageIdeleToBottom a F) (by rfl) x

end
end Dubon2026
