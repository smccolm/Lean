import Dubon2026.SourceCurveSeparableDifferentialBaseChange
import Dubon2026.SourceCurveFiniteCoordinateCanonical
import Dubon2026.SourceCurveFiniteCoordinateExtension
import Dubon2026.SourceModularCoefficientLocalDifferentials

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
unramified-cover genus. Every finite extension of the actual arithmetic
modular field has the required actual curve structure and canonical
divisors. In particular these conclusions apply to the finite prime
Kummer cover. The original nonzero j differential survives separable
base change; no curve structure or canonical support is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve IntermediateField KaehlerDifferential
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
theorem modular_extension_finite_coordinate
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E]
    [IsScalarTower Qbar FF E] [FiniteDimensional FF E] :
    FiniteDimensional Qbar⟮algebraMap FF E (jCoeff N Qbar)⟯ E := by
  letI hdim : FiniteDimensional Qbar⟮jCoeff N Qbar⟯ FF := finiteDimensional_coeff_field N Qbar
  apply Module.finite_of_finrank_pos
  rw [finrank_adjoin_algebraMap_mul]
  exact Nat.mul_pos Module.finrank_pos Module.finrank_pos

omit [NeZero N] in
theorem modular_extension_D_j_ne_zero
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E]
    [IsScalarTower Qbar FF E] [FiniteDimensional FF E] :
    D Qbar E (algebraMap FF E (jCoeff N Qbar)) ≠ 0 := by
  letI : CharZero FF := charZero_of_injective_algebraMap (algebraMap Qbar FF).injective
  exact D_algebraMap_ne_zero_of_separable (D_jCoeff_ne_zero N Qbar)

theorem modular_extension_curve_and_canonical
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E]
    [IsScalarTower Qbar FF E] [FiniteDimensional FF E] :
    IsCurveOver Qbar E ∧ HasCanonicalDivisor (K := Qbar) (F := E) := by
  letI hdim : FiniteDimensional Qbar⟮algebraMap FF E (jCoeff N Qbar)⟯ E :=
    modular_extension_finite_coordinate N E
  have ht : Transcendental Qbar (algebraMap FF E (jCoeff N Qbar)) :=
    (transcendental_algebraMap_iff (algebraMap FF E).injective).mpr (transcendental_jCoeff N Qbar)
  have hDt := modular_extension_D_j_ne_zero N E
  exact ⟨isCurveOver_finite_coordinate _ ht hDt,
    hasCanonicalDivisor_finite_coordinate _ ht hDt⟩

end
end Dubon2026.SourceFunctionField
