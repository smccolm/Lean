import Dubon2026.SourceGammaOneComplexCoefficientMap
import Dubon2026.SourceOriginalComplexFieldExtension

/-! DUB17/18 -> original all-weight arithmetic realization -> Gamma1
arithmetic/complex Picard torsion comparison -> actual constant-field
extension. The chosen original coefficient embedding gives compatible
scalar towers. The literal Laurent scalar-extension generators prove
that complex constants and the arithmetic field image generate the
entire actual Gamma1 complex field; no two-generator presentation is
needed or assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ)
local notation "FQ" => functionFieldOver (Gamma1 N) Qbar
local notation "FC" => functionFieldOver (Gamma1 N) ℂ

/-- Complex scalars with the same fixed original algebraic-closure embedding. -/
abbrev complexAlgebra : Algebra Qbar ℂ := OriginalConstantField.complexAlgebra

/-- The actual arithmetic Gamma1 field acts through its proved coefficient embedding. -/
abbrev fieldAlgebra : Algebra FQ FC := (fieldMap N).toAlgebra

/-- The common algebraic-closure scalar action on the actual Gamma1 complex field. -/
abbrev complexFieldAlgebra : Algebra Qbar FC :=
  ((algebraMap ℂ FC).comp OriginalConstantField.sigma.toRingHom).toAlgebra

attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra

theorem complexScalarTower : IsScalarTower Qbar ℂ FC :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem arithmeticFieldScalarTower : IsScalarTower Qbar FQ FC :=
  IsScalarTower.of_algebraMap_eq fun a => (fieldMap_constants N a).symm

theorem adjoin_range_fieldMap :
    IntermediateField.adjoin ℂ (Set.range (fieldMap N)) = ⊤ := by
  apply IntermediateField.lift_injective (functionFieldOver (Gamma1 N) ℂ)
  refine Eq.trans ?_ (IntermediateField.lift_top ℂ
    (functionFieldOver (Gamma1 N) ℂ)).symm
  apply le_antisymm (IntermediateField.lift_le _)
  change IntermediateField.adjoin ℂ
    (coeffEmb ℂ '' (qExpFunctionFieldC ℚ (Gamma1 N) : Set (LaurentSeries ℚ))) ≤ _
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨coeffEmb ℂ x, coeffEmb_mem_laurentBaseChange ℂ hx⟩, ?_, rfl⟩
  exact IntermediateField.subset_adjoin ℂ _
    ⟨⟨coeffEmb Qbar x, coeffEmb_mem_laurentBaseChange Qbar hx⟩,
      fieldMap_rational N ⟨x, hx⟩⟩

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
