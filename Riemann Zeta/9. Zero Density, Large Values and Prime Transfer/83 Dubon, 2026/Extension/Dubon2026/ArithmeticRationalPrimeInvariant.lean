import Dubon2026.ArithmeticOriginalBottomCompletionInvariant
import Dubon2026.ArithmeticOriginalBottomPrimeEquiv
import Dubon2026.OriginalPrimeTowerSelection
import Dubon2026.ArithmeticRelativePrimeCompletionComparison

/-! The actual rational canonical total indexed by original rational
number-field primes. The original bottom-field class and literal prime
contraction are retained. This supplies DUB-17's canonical total comparison
before the exceptional local Cartier family is substituted. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField BigOperators
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  bottomInvariantStageAlgebra bottomInvariantStageModule bottomInvariantStageSMul
  bottomInvariantStageTower bottomInvariantStageRationalGalois bottomInvariantStageGalois
  bottomInvariantStageFinite

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))

/-- The canonical prime coordinate of the actual rational-base idele class,
using its proved corresponding bottom-field prime. -/
def arithmeticCommonStageRationalPrimeInvariant (v : HeightOneSpectrum (𝓞 ℚ)) :
    groupCohomology (originalFullIdeleRep ℚ F) 2 →+ AddCircle (1 : ℚ) :=
  (rationalArithmeticRelativeStageIdelePrimeInvariant a ⊥ F.toIntermediateField bot_le
    ((arithmeticOriginalBottomPrimeEquiv a).symm v)).comp
      (arithmeticCommonStageIdeleToBottom a F)


/-- The actual corresponding bottom-field prime lies over the specified rational prime. -/
theorem arithmeticOriginalBottomPrimeEquiv_symm_liesOver
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((arithmeticOriginalBottomPrimeEquiv a).symm v).asIdeal.LiesOver v.asIdeal := by
  constructor
  exact (congrArg HeightOneSpectrum.asIdeal
    ((arithmeticOriginalBottomPrimeEquiv a).apply_symm_apply v)).symm


/-- An original upper prime above the rational prime lies over its unique
bottom-field counterpart; no additional prime choice is assumed. -/
theorem arithmeticOriginalBottomPrimeEquiv_upper_liesOver
    (v : HeightOneSpectrum (𝓞 ℚ)) (w : HeightOneSpectrum (𝓞 F))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.LiesOver ((arithmeticOriginalBottomPrimeEquiv a).symm v).asIdeal := by
  have h : originalFinitePrimeBelow (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F w =
      (arithmeticOriginalBottomPrimeEquiv a).symm v := by
    apply (arithmeticOriginalBottomPrimeEquiv a).injective
    change originalFinitePrimeBelow ℚ (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a))
      (originalFinitePrimeBelow (⊥ : IntermediateField ℚ (rationalUnramifiedExtension a)) F w) = _
    rw [originalFinitePrimeBelow_tower,
      originalFinitePrimeBelow_eq_of_liesOver ℚ F v w]
    exact ((arithmeticOriginalBottomPrimeEquiv a).apply_symm_apply v).symm
  constructor
  exact (congrArg HeightOneSpectrum.asIdeal h).symm

end
end Dubon2026
