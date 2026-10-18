import Dubon2026.ArithmeticRationalInvariantApply
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

/-- The actual canonical total is the sum of its original rational-prime
coordinates, through the proved prime-contraction bijection. -/
theorem arithmeticCommonStageRationalIdeleTotal_eq_finsum
    (x : groupCohomology (originalFullIdeleRep ℚ F) 2) :
    arithmeticCommonStageRationalIdeleTotal a F x =
      ∑ᶠ v, arithmeticCommonStageRationalPrimeInvariant a F v x := by
  have hindex := (finsum_comp_equiv (arithmeticOriginalBottomPrimeEquiv a).symm
    (f := fun u => rationalArithmeticRelativeStageIdelePrimeInvariant
      (hGal := bottomInvariantStageGalois a F) a ⊥ F.toIntermediateField
      bot_le u (arithmeticCommonStageIdeleToBottom a F x))).symm
  exact (arithmeticCommonStageRationalIdeleTotal_apply a F x).trans
    ((rationalArithmeticRelativeStageIdeleTotalInvariant_apply
      (hGal := bottomInvariantStageGalois a F) a ⊥ F.toIntermediateField bot_le
      (arithmeticCommonStageIdeleToBottom a F x)).trans
      (hindex.trans (congrArg (fun f : HeightOneSpectrum (𝓞 ℚ) → AddCircle (1 : ℚ) => ∑ᶠ v, f v)
        (funext (fun v => (arithmeticCommonStageRationalPrimeInvariant_apply a F v x).symm)))))


end
end Dubon2026
