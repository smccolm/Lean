import Dubon2026.SourceConstantFieldCoordinateSpan
import Dubon2026.SourceGammaOneComplexFieldExtension
import Dubon2026.SourceGammaOneDegreeBaseChange

/-! DUB-17/18 -> original Picard injectivity -> principal-divisor descent
-> trace reconstruction in corresponding coordinate bases. The original
coordinate degree is already known to be unchanged under every constant
extension. Therefore spanning gives a basis by the native dimension theorem;
no new denominator-clearing independence argument is required.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => functionFieldOver (Gamma1 N) Qbar
local notation "FC" => functionFieldOver (Gamma1 N) ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower arithmeticFieldScalarTower

theorem exists_complex_coordinate_basis {n : ℕ}
    (y : Module.Basis (Fin n) (IntermediateField.adjoin Qbar (Set.singleton (jCoordinateOver (Gamma1 N) Qbar))) FQ) :
    ∃ y' : Module.Basis (Fin n)
        (IntermediateField.adjoin ℂ (Set.singleton (algebraMap FQ FC (jCoordinateOver (Gamma1 N) Qbar)))) FC,
      ∀ i, y' i = fieldMap N (y i) := by
  letI := finiteDimensional_jCoordinateOver (Γ := Gamma1 N)
    (by simp [Gamma1_mem, ModularGroup.T]) Qbar
  apply SourceCurve.ConstantField.exists_coordinate_basis_of_finrank_eq (K := Qbar) (K' := ℂ)
    (adjoin_range_fieldMap N) (jCoordinateOver (Gamma1 N) Qbar) y
  change n = Module.finrank (IntermediateField.adjoin ℂ
    (Set.singleton (fieldMap N (jCoordinateOver (Gamma1 N) Qbar)))) FC
  rw [fieldMap_j]
  exact ((Fintype.card_fin n).symm.trans (Module.finrank_eq_card_basis y).symm).trans
    ((finrank_over_j_baseChange N Qbar).trans (finrank_over_j_baseChange N ℂ).symm)

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
