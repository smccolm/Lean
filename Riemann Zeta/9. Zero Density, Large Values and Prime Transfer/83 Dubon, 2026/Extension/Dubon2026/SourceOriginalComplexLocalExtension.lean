import Dubon2026.SourceOriginalComplexFieldIndependence
import Dubon2026.SourceConstantFieldLocalFractions
import Dubon2026.SourceConstantFieldLocalDecomposition
import Dubon2026.SourceOriginalResidueFinite

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> exact
extension of original places. Every original complex function is a fraction
of finite local combinations at the chosen arithmetic place. Every nonzero
coefficient vector has a first nonzero residue digit after finitely many
uniformizer factors. Exact original image generation and finite original
residue fields discharge the generic algebraic prerequisites. The resulting
form is used to prove order preservation and uniqueness of the extended place.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower
variable {ι : Type*} (B : Module.Basis ι Qbar ℂ)
  (P : Place Qbar (modularFunctionFieldOver N Qbar))

theorem original_local_fraction {z : modularFunctionFieldOver N ℂ} (hz : z ≠ 0) :
    ∃ w₁ w₂, ConstantField.Psi (modularFunctionFieldOver N ℂ) B P w₂ ≠ 0 ∧
      z * ConstantField.Psi (modularFunctionFieldOver N ℂ) B P w₂ =
        ConstantField.Psi (modularFunctionFieldOver N ℂ) B P w₁ :=
  ConstantField.exists_mul_Psi_eq _ B P (adjoin_range_fieldMap N) hz

theorem original_local_expansion {π : P.toValuationSubring} (hπ : Irreducible π)
    (w : ι →₀ P.toValuationSubring) (hw : w ≠ 0) :
    ∃ (k : ℕ) (d : ℂ) (w' : ι →₀ P.toValuationSubring), d ≠ 0 ∧
      ConstantField.Psi (modularFunctionFieldOver N ℂ) B P w =
        fieldMap N (π : modularFunctionFieldOver N Qbar) ^ k *
          (algebraMap ℂ (modularFunctionFieldOver N ℂ) d +
            fieldMap N (π : modularFunctionFieldOver N Qbar) *
              ConstantField.Psi (modularFunctionFieldOver N ℂ) B P w') := by
  letI : Module.Finite Qbar P.ResidueField := finite_original_place_residue N Qbar P
  exact ConstantField.decomp _ B P hπ w hw

end
end Dubon2026.SourceFunctionField.OriginalConstantField
