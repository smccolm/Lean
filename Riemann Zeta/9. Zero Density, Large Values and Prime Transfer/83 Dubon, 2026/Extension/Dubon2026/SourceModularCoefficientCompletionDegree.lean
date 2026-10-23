import Dubon2026.SourceCurveCompletionDegree
import Dubon2026.SourceModularCoefficientLocalFieldTrace

/-! Every actual modular coefficient-field completion has degree equal to
its original ramification index over the j-coordinate field. The actual
residue fields are rational, so completed inertia is one. This is the
dimension input for assembling the local field-trace identities over all
places in the DUB-17/18 global-residue argument. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

/-- The actual completed modular degree equals the original j-coordinate ramification index. -/
theorem coeff_completion_finrank_eq_ramificationIndex (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K]
    (w : Place K (modularFunctionFieldCoeff N K)) :
    let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
      IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
    letI : Algebra K J := J.toSubalgebra.algebra
    letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
    letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
    letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
    w.completedExtensionDegree (F := J) = w.ramificationIndex (F := J) := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  letI : Algebra.IsSeparable J (modularFunctionFieldCoeff N K) := isSeparable_coeff_field N K
  exact w.completion_finrank_eq_ramificationIndex (F := J)
    (coeff_place_residue_algebraMap_bijective N K w).surjective

end Dubon2026.SourceFunctionField
