import Dubon2026.ContinuousGaloisBaseChangeFiniteStage

/-! # Original finite Galois stages under extension of the fixed base -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- Regard the same original finite field H as a finite Galois
intermediate field over the original smaller stage E. Its elements and
ambient inclusion are unchanged. -/
def finiteGaloisStageExtendScalars (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) :
    FiniteGaloisIntermediateField E Ω where
  toIntermediateField := IntermediateField.extendScalars hEH
  finiteDimensional := by
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    haveI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    exact FiniteDimensional.right K E H
  isGalois := by
    letI : Algebra E H := (IntermediateField.inclusion hEH).toAlgebra
    haveI : IsScalarTower K E H := IsScalarTower.of_algHom (IntermediateField.inclusion hEH)
    exact IsGalois.tower_top_of_isGalois K E H

/-- Extending the fixed base retains the exact original ambient set. -/
theorem finiteGaloisStageExtendScalars_coe
    (E H : FiniteGaloisIntermediateField K Ω) (hEH : E ≤ H) :
    ((finiteGaloisStageExtendScalars E H hEH).toIntermediateField : Set Ω) =
      (H.toIntermediateField : Set Ω) := by
  rfl

end
end Dubon2026
