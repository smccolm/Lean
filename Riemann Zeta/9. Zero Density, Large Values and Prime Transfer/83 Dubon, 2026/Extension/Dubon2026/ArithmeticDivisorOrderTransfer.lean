import Dubon2026.ArithmeticRelativeStageClassProjection
import Dubon2026.ArithmeticRelativeStageIdeleBaseChange
import Dubon2026.OriginalIntermediateDivisorOrderTransfer

/-! # The arithmetic interface for prescribed class order

This discharges the indicated prime-power order obligation inside DUB-17's
mixed-degree full-order class construction. The original field and cohomology
maps are retained. No general cyclic auxiliary extension is required.
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
  [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]

/-- The original field-tower generator theorem applies to the literal arithmetic class projection and full-idele base change; no map-identification premise is supplied. -/
theorem rationalArithmeticRelativeStage_class_order_of_idele
    (d n' : ℕ) (hd0 : d ≠ 0) (hn'0 : n' ≠ 0) (hd : d ∣ n')
    (x : rationalArithmeticRelativeStageIdeleH2 a K L hKL)
    (ho : addOrderOf (rationalArithmeticRelativeStageClassProjection a K L hKL x) = n')
    (hz : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      rationalArithmeticRelativeStageClassProjection a E M hEM
        ((n' / d) •
          rationalArithmeticRelativeStageIdeleBaseChange a K E L M hKE hKL hEM hLM x) = 0) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Module K E := Algebra.toModule
    ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      addOrderOf y = d := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  exact originalIntermediateField_class_order_of_idele
    (hGalKE := hGalKE) (hGalKL := hGalKL) (hGalKM := hGalKM)
    (rationalUnramifiedExtension a) K E L M hKE hKL hEM hLM d n' hd0 hd hn'0 x ho hz

end
end Dubon2026
