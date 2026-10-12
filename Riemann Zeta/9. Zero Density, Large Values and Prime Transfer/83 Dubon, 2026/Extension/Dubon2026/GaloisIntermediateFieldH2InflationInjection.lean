import Dubon2026.GaloisFixedFieldH2InflationInjection

/-! # Actual H2 inflation is injective for every original normal intermediate field -/

namespace Dubon2026
noncomputable section

open CategoryTheory

/-- Reconstructing an original normal intermediate field as the fixed
field of its original fixing subgroup proves injectivity of the literal
unit-cohomology field inclusion and automorphism restriction map. -/
theorem galoisIntermediateFieldH2Inflation_mono
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (F : IntermediateField K L) [IsGalois K F] :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom F)
      (finiteGaloisUnitTowerInclusion K F L) 2) := by
  let Q : IntermediateField K L → Prop := fun E =>
    ∀ [IsGalois K E], Mono (groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (finiteGaloisUnitTowerInclusion K E L) 2)
  have h : Q (IntermediateField.fixedField F.fixingSubgroup) := by
    intro hE
    exact galoisFixedFieldH2Inflation_mono F.fixingSubgroup
  have hF : Q F := (congrArg Q (IsGalois.fixedField_fixingSubgroup F)).mp h
  exact hF

end
end Dubon2026
