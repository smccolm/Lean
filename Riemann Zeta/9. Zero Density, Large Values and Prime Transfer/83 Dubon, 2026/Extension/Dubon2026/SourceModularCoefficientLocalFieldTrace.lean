import Dubon2026.SourceCurveCompletionTraceUniformizer
import Dubon2026.SourceModularCoefficientCompletionTrace
import Dubon2026.SourceModularCoefficientIntegralBasis

/-! The actual modular coefficient-field residue against the restricted
j-coordinate uniformizer is computed by the literal completed field trace.
Finite degree, separability, residue rationality and the integral basis are
all derived. This supplies the local trace identity needed before summing
over actual places in the DUB-17/18 global-residue argument. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

/-- The literal modular field satisfies the completed local field-trace identity. -/
theorem coeff_tateResidue_completion_fieldTrace_uniformizer (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K]
    (w : Place K (modularFunctionFieldCoeff N K)) :
    let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
      IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
    letI : Algebra K J := J.toSubalgebra.algebra
    letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
    letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
    letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
    ∀ f : modularFunctionFieldCoeff N K,
      w.tateResidue f (algebraMap J (modularFunctionFieldCoeff N K) (w.restrict J).uniformizer) =
        (w.restrict J).completionPlace.tateResidue
          (Algebra.trace (w.restrict J).adicCompletion w.adicCompletion
            (w.completionLinearMap f))
          ((w.restrict J).completionLinearMap (w.restrict J).uniformizer) := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  letI : Algebra.IsSeparable J (modularFunctionFieldCoeff N K) := isSeparable_coeff_field N K
  refine fun f => ?_
  exact w.tateResidue_completion_fieldTrace_uniformizer (F := J)
    (coeff_place_residue_algebraMap_bijective N K w).surjective f

end Dubon2026.SourceFunctionField
