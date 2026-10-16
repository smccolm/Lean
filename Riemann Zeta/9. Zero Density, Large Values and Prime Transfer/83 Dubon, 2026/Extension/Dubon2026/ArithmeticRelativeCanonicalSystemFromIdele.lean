import Dubon2026.ArithmeticRelativeCanonicalComparisonAssembly
import Dubon2026.OriginalIntermediateFieldCanonicalClassSystem
import Dubon2026.ArithmeticRelativeIdeleVerticalTotal
import Dubon2026.ArithmeticPrimePowerIdeleKernelTotal

/-! # Actual arithmetic class normalization from an auxiliary idele

The vertical canonical-total comparisons and the odd-primary principal
kernel theorem discharge every reciprocity input of the native auxiliary
argument. The remaining witness premises are precisely those returned by
the existing single-prime construction on DUB-17's arithmetic tower.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageIdeleAddCommGroup
  arithmeticRelativeStageClassAddCommGroup

variable (a : 𝓞 ℚ)
  (K E L M : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]

/-- The original normalized class system with its canonical total formula follows from the actual auxiliary idele witness; vertical and principal compatibility are proved internally. -/
theorem rationalArithmeticRelativeStage_normalized_system_of_auxiliary_idele
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegreeKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
      letI : Module K M := Algebra.toModule
      Module.finrank K M = q ^ t)
    (n : ℕ) (hn : n ≠ 0)
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E ∣ n)
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (ho : addOrderOf (rationalArithmeticRelativeStageClassProjection a K L hKL x) = n)
    (hz : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      rationalArithmeticRelativeStageClassProjection a E M hEM
        ((n / Module.finrank K E) •
          rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0)
    (ht : rationalArithmeticRelativeStageIdeleTotalInvariant a K L hKL x = ↑((1 : ℚ) / n)) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    OriginalCanonicalClassInvariantSystem K E
      (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE) := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact rationalArithmeticRelativeStage_normalized_system_of_auxiliary_comparisons
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalKM := hGalKM)
    a K E L M hKE hKL hEM hLM
    (rationalArithmeticRelativeStageIdeleBaseChange_vertical_total
      (hGalKL := hGalKE) (hGalKM := hGalKM) a K E M hKE hEM)
    (rationalArithmeticRelativeStageIdeleBaseChange_vertical_total
      (hGalKL := hGalKL) (hGalKM := hGalKM) a K L M hKL hLM)
    (rationalArithmeticRelativePrimePower_total_zero_of_class_zero
      (hGalKE := hGalKM) a K M (hKE.trans hEM) q t hq hq2 hqa hdegreeKM)
    n hn hd x ho hz ht

end
end Dubon2026
