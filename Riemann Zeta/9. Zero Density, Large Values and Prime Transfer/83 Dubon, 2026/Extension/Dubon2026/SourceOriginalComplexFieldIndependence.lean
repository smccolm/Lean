import Dubon2026.SourceOriginalComplexFieldExtension
import Dubon2026.SourceLaurentScalarIndependence

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> original constant-field place transport. The literal Laurent coefficients preserve
linear independence of every original function-field family under the chosen
Qbar-to-complex embedding. This supplies the linear-disjointness input directly,
without a general irreducibility theorem for arbitrary constant-field curves.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
variable (N : ℕ)

/-- Inclusion into Laurent series with their coefficientwise scalar action. -/
def originalLaurentLinearMap (L : Type*) [Field L] [Algebra ℚ L] :
    modularFunctionFieldOver N L →ₗ[L] LaurentSeries L where
  toFun := Subtype.val
  map_add' _ _ := rfl
  map_smul' a x := by
    change algebraMap L (LaurentSeries L) a * (x : LaurentSeries L) = a • (x : LaurentSeries L)
    rw [SourceDifferential.algebraMap_laurentSeries_apply_alt,
      HahnSeries.single_zero_mul_eq_smul]

theorem fieldMap_linearIndependent {ι : Type*} {v : ι → modularFunctionFieldOver N Qbar}
    (hv : LinearIndependent Qbar v) :
    LinearIndependent ℂ (fun i => fieldMap N (v i)) := by
  have hcoeff : LinearIndependent Qbar (fun i => (v i : LaurentSeries Qbar)) :=
    hv.map' (originalLaurentLinearMap N Qbar)
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have h := linearIndependent_coeffMap_algebraMap ℂ hcoeff
  exact LinearIndependent.of_comp (originalLaurentLinearMap N ℂ) h

end
end Dubon2026.SourceFunctionField.OriginalConstantField
