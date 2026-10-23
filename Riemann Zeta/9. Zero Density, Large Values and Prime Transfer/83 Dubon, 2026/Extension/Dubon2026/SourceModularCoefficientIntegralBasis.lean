import Dubon2026.SourceCurveCompletionIntegralBasis
import Dubon2026.SourceModularCoefficientCompletions

/-! The actual integral basis for each modular coefficient-field completion
over its j-coordinate completion. All finite-degree, separability, spectral
integrality, localization and freeness inputs are derived. This removes
the integral-basis assumption from the remaining local residue/field-trace
comparison on the DUB-17/18 reverse-genus dependency path. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

/-- Every actual modular completion has a field basis detecting its literal integral ring. -/
theorem coeff_completion_integral_basis (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [PerfectField K]
    (w : Place K (modularFunctionFieldCoeff N K)) :
    let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
      IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
    letI : Algebra K J := J.toSubalgebra.algebra
    letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
    letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
    letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
    Nonempty (w.CompletionIntegralBasis (F := J)) := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  letI : Algebra.IsSeparable J (modularFunctionFieldCoeff N K) := isSeparable_coeff_field N K
  exact w.completionIntegralBasis_nonempty (F := J)

end Dubon2026.SourceFunctionField
