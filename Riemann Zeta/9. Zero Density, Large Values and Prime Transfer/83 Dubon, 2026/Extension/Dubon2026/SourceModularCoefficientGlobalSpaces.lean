import Dubon2026.SourceCurvePrincipalGlobalConstants
import Dubon2026.SourceCurveSeparatingPoleDegree
import Dubon2026.SourceModularCoefficientCurve
import Dubon2026.SourceCurveLSpaceFinite

/-! DUB-17/18 -> actual modular good reduction -> residue genus comparison.
For the literal all-divisor coefficient field, j supplies a place and the
proved principal-divisor and residue theorems supply the other hypotheses.
All divisor spaces are finite and the global regular functions are exactly
the constants, including in characteristics two and three. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

theorem nonempty_coeff_place : Nonempty (Place K (modularFunctionFieldCoeff N K)) := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  exact nonempty_place_of_separating_coordinate (jCoeff N K) (transcendental_jCoeff N K)

theorem coeff_lSpace_zero_eq_range :
    LSpace (0 : Divisor K (modularFunctionFieldCoeff N K)) =
      LinearMap.range (Algebra.linearMap K (modularFunctionFieldCoeff N K)) := by
  haveI := hasPrincipalDivisors_coeff_field N K
  haveI := finite_coeff_place_residue N K
  exact lSpace_zero_eq_range_of_principalDivisors (nonempty_coeff_place N K).some

theorem finite_coeff_lSpace (D : Divisor K (modularFunctionFieldCoeff N K)) :
    Module.Finite K (LSpace D) := by
  haveI := finite_coeff_place_residue N K
  haveI : Module.Finite K (LSpace (0 : Divisor K (modularFunctionFieldCoeff N K))) := by
    rw [coeff_lSpace_zero_eq_range N K]
    infer_instance
  exact finite_lSpace D

theorem finrank_coeff_lSpace_zero :
    Module.finrank K (LSpace (0 : Divisor K (modularFunctionFieldCoeff N K))) = 1 := by
  rw [coeff_lSpace_zero_eq_range N K,
    LinearMap.finrank_range_of_inj (f := Algebra.linearMap K (modularFunctionFieldCoeff N K))
      (algebraMap K (modularFunctionFieldCoeff N K)).injective, Module.finrank_self]

end
end Dubon2026.SourceFunctionField
