import Dubon2026.SourceCurveSeparatingFunctionSupport
import Dubon2026.SourceModularCoefficientSeparability

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> principal
divisors on the actual residue curve. Every literal function now has finite
normalized-order support over perfect constants. The degree-zero assertion
is a separate remaining obligation; it is not assumed here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem finite_coeff_divisor_support (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [PerfectField K] (f : modularFunctionFieldCoeff N K) :
    {v : SourceCurve.Place K (modularFunctionFieldCoeff N K) | v.ord f ≠ 0}.Finite := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  exact SourceCurve.finite_function_support_of_separating_coordinate
    (jCoeff N K) (transcendental_jCoeff N K) f

end
end Dubon2026.SourceFunctionField
