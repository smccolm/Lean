import Dubon2026.OriginalIntermediateFieldCanonicalClassSystem
import Dubon2026.ArithmeticRelativeIdeleVerticalTotal
import Dubon2026.ArithmeticPrimePowerIdeleKernelTotal

/-! # Actual arithmetic class normalization from an auxiliary idele

Resolve the literal arithmetic maps in the native auxiliary argument.
Vertical comparison and principal-kernel vanishing remain explicit, narrower
inputs here; the adjacent arithmetic theorem derives them. Factoring this
application keeps DUB-17's exact map identifications within default limits.
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

/-- The original normalized class system with its canonical total formula follows from the actual auxiliary idele witness; vertical and principal compatibility are explicit upstream premises. -/
theorem rationalArithmeticRelativeStage_normalized_system_of_auxiliary_comparisons
    (hE : ∀ z : rationalArithmeticRelativeStageIdeleH2 a K E hKE,
      rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM)
        (rationalArithmeticRelativeStageIdeleBaseChange a K K E M le_rfl hKE (hKE.trans hEM) hEM z) =
          rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE z)
    (hL : ∀ z : rationalArithmeticRelativeStageIdeleH2 a K L hKL,
      rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKL.trans hLM)
        (rationalArithmeticRelativeStageIdeleBaseChange a K K L M le_rfl hKL (hKL.trans hLM) hLM z) =
          rationalArithmeticRelativeStageIdeleTotalInvariant a K L hKL z)
    (hkernel : ∀ z : rationalArithmeticRelativeStageIdeleH2 a K M (hKE.trans hEM),
      rationalArithmeticRelativeStageClassProjection a K M (hKE.trans hEM) z = 0 →
        rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM) z = 0)
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
  exact originalIntermediateField_normalized_system_of_auxiliary_idele
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalKM := hGalKM)
    (rationalUnramifiedExtension a) K E L M hKE hKL hEM hLM
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE)
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K L hKL)
    (rationalArithmeticRelativeStageIdeleTotalInvariant a K M (hKE.trans hEM))
    hE hL hkernel n hd hn x ho hz ht

end
end Dubon2026
