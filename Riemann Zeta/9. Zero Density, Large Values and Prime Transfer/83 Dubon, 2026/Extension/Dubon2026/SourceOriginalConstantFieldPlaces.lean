import Dubon2026.SourceOriginalConstantFieldValuationExtension
import Dubon2026.SourceConstantFieldExtensionOrders
import Dubon2026.SourceCurveFiniteCoordinateValuations
import Dubon2026.SourceOriginalResidueFinite

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> actual
divisor conorm. Every arithmetic place extends uniquely to the original complex
field, and every original function retains exactly its normalized integer
order. The original field generation, coefficient independence, finite residue
fields and finite transcendental coordinate supply all upstream hypotheses.
This provides the actual place map needed for principal-divisor transport.
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

theorem exists_original_extended_place (P : Place Qbar FQ) :
    ∃ Q : Place ℂ FC,
      Q.toValuationSubring.comap (fieldMap N) = P.toValuationSubring ∧
      (∀ f : FQ, Q.ord (fieldMap N f) = P.ord f) ∧
      ∀ Q' : Place ℂ FC,
        Q'.toValuationSubring.comap (fieldMap N) = P.toValuationSubring → Q' = Q := by
  obtain ⟨V, hV, hC, hP⟩ := exists_extending_valuation N P
  letI := finiteDimensional_original N ℂ
  obtain ⟨Q, hQ⟩ := ConstantField.exists_place_of_finite_coordinate
    (jOver N ℂ) (transcendental_jOver N ℂ) V hC hV
  have hover : Q.toValuationSubring.comap (fieldMap N) = P.toValuationSubring := by
    rw [hQ]
    exact hP
  letI : Module.Finite Qbar P.ResidueField := finite_original_place_residue N Qbar P
  obtain ⟨hord, huniq⟩ := ConstantField.extension_order_and_unique FC P (adjoin_range_fieldMap N)
  exact ⟨Q, hover, hord Q hover, fun Q' hQ' => huniq Q' Q hQ' hover⟩

end
end Dubon2026.SourceFunctionField.OriginalConstantField
