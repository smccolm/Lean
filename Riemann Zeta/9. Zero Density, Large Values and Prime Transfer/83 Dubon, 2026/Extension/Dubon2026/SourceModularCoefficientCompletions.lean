import Dubon2026.SourceCurveCompletionSeparable
import Dubon2026.SourceModularCoefficientSeparability

/-! The actual coefficient modular field has a finite separable completed
extension over its literal j-coordinate completion at every place. The
coordinate degree and separability are derived from the existing modular
field results. These supply the local field inputs for the integral basis
and residue/trace compatibility in the reverse-genus proof, DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

/-- The actual modular coefficient-field completion is finite and separable over its j completion. -/
theorem coeff_completion_finite_separable (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [PerfectField K]
    (w : Place K (modularFunctionFieldCoeff N K)) :
    let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
      IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
    letI : Algebra K J := J.toSubalgebra.algebra
    letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
    letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
    letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
    FiniteDimensional (w.restrict J).adicCompletion w.adicCompletion ∧
      Algebra.IsSeparable (w.restrict J).adicCompletion w.adicCompletion := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  letI : Algebra.IsSeparable J (modularFunctionFieldCoeff N K) := isSeparable_coeff_field N K
  exact ⟨w.finiteDimensional_completion (F := J), w.isSeparable_completion (F := J)⟩

end Dubon2026.SourceFunctionField
