import Dubon2026.ArithmeticRelativeStageClassProjection
import Dubon2026.ArithmeticRelativeStageIdeleBaseChange
import Dubon2026.OriginalIntermediateFieldGeneratorTransfer

/-! # The actual arithmetic interface to original generator transfer

Resolve the genuine finite field algebras and towers once, then apply
the existing original class transfer. This preserves all original maps
while keeping DUB-17's constructed-witness assembly within default limits.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField Classical
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

/-- The original field-tower generator theorem applies to the literal arithmetic class projection and full-idele base change; no map-identification premise is supplied. -/
theorem rationalArithmeticRelativeStage_class_generator_of_idele
    (n' : ℕ) (hn'0 : n' ≠ 0)
    (hd : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E ∣ n')
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (ho : addOrderOf (rationalArithmeticRelativeStageClassProjection a K L hKL x) = n')
    (hz : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      rationalArithmeticRelativeStageClassProjection a E M hEM
        ((n' / Module.finrank K E) •
          rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
      Submodule.span ℤ {y} = ⊤ := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact originalIntermediateField_class_generator_of_idele
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalKM := hGalKM)
    (rationalUnramifiedExtension a) K E L M hKE hKL hEM hLM n' hd hn'0 x ho hz

end
end Dubon2026
