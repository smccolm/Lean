import Dubon2026.SourceOriginalComplexCoefficientMap

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> constant-field
place transport. The actual coefficient embedding and its two scalar towers
generate exactly the original complex field, by the already proved pair theorem.
These are the concrete hypotheses needed for divisor extension and descent.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ)

/-- Complex scalars with the chosen original algebraic-closure embedding. -/
abbrev complexAlgebra : Algebra Qbar ℂ := sigma.toRingHom.toAlgebra

/-- The original arithmetic function field acts through its coefficient embedding. -/
abbrev fieldAlgebra :
    Algebra (modularFunctionFieldOver N Qbar) (modularFunctionFieldOver N ℂ) :=
  (fieldMap N).toAlgebra

/-- The common algebraic-closure scalar action on the original complex field. -/
abbrev complexFieldAlgebra : Algebra Qbar (modularFunctionFieldOver N ℂ) :=
  ((algebraMap ℂ (modularFunctionFieldOver N ℂ)).comp sigma.toRingHom).toAlgebra

attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra

theorem complexScalarTower : IsScalarTower Qbar ℂ (modularFunctionFieldOver N ℂ) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem originalFieldScalarTower :
    IsScalarTower Qbar (modularFunctionFieldOver N Qbar) (modularFunctionFieldOver N ℂ) :=
  IsScalarTower.of_algebraMap_eq fun a => (fieldMap_constants N a).symm

theorem adjoin_range_fieldMap [NeZero N] :
    IntermediateField.adjoin ℂ (Set.range (fieldMap N)) = ⊤ := by
  apply top_unique
  rw [← original_internal_pair_adjoin_top N ℂ, IntermediateField.adjoin_le_iff]
  rintro x (rfl | hx)
  · exact IntermediateField.subset_adjoin ℂ _ ⟨jOver N Qbar, fieldMap_j N⟩
  · rcases hx with rfl
    exact IntermediateField.subset_adjoin ℂ _ ⟨jNOver N Qbar, fieldMap_jN N⟩

end
end Dubon2026.SourceFunctionField.OriginalConstantField
