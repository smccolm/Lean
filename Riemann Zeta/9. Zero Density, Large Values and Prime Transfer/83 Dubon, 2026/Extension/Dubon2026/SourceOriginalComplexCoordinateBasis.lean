import Dubon2026.SourceConstantFieldCoordinateSpan
import Dubon2026.SourceOriginalComplexFieldExtension
import Dubon2026.SourceOriginalDegreeBaseChange

/-! DUB-17/18 -> original Picard injectivity -> principal-divisor descent
-> trace reconstruction in corresponding coordinate bases. The original
coordinate degree is already known to be unchanged under every constant
extension. Therefore spanning gives a basis by the native dimension theorem;
no new denominator-clearing independence argument is required.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

theorem exists_original_complex_coordinate_basis {n : ℕ}
    (y : Module.Basis (Fin n) (IntermediateField.adjoin Qbar (Set.singleton (jOver N Qbar))) FQ) :
    ∃ y' : Module.Basis (Fin n)
        (IntermediateField.adjoin ℂ (Set.singleton (algebraMap FQ FC (jOver N Qbar)))) FC,
      ∀ i, y' i = fieldMap N (y i) := by
  letI := finiteDimensional_original N Qbar
  apply ConstantField.exists_coordinate_basis_of_finrank_eq (K := Qbar) (K' := ℂ)
    (adjoin_range_fieldMap N) (jOver N Qbar) y
  change n = Module.finrank (IntermediateField.adjoin ℂ
    (Set.singleton (fieldMap N (jOver N Qbar)))) FC
  rw [fieldMap_j]
  exact ((Fintype.card_fin n).symm.trans (Module.finrank_eq_card_basis y).symm).trans
    ((finrank_original_over_j_baseChange N Qbar).trans (finrank_original_over_j_baseChange N ℂ).symm)

end
end Dubon2026.SourceFunctionField.OriginalConstantField
