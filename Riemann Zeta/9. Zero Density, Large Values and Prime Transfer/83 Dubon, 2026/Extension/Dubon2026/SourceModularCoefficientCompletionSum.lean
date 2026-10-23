import Dubon2026.SourceCurveFiberCompletionTrace
import Dubon2026.SourceModularCoefficientCompletionDegree

/-! The actual modular coefficient-field trace is the sum of its completed
local traces above each restricted j-coordinate place. All rationality,
finite-degree and separability hypotheses are derived for the literal
field. This removes the product-decomposition input from the DUB-17/18
global residue argument. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

/-- The literal modular field trace splits over its actual completion fiber. -/
theorem coeff_completionTraceSum (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K]
    (w : Place K (modularFunctionFieldCoeff N K)) :
    let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
      IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
    letI : Algebra K J := J.toSubalgebra.algebra
    letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
    letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
    letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
    ∀ g : modularFunctionFieldCoeff N K,
      (w.restrict J).completionLinearMap (Algebra.trace J (modularFunctionFieldCoeff N K) g) =
        ∑ᶠ z : {z : Place K (modularFunctionFieldCoeff N K) // z.restrict J = w.restrict J},
          Algebra.trace (w.restrict J).adicCompletion z.1.adicCompletion
            (z.1.completionLinearMap g) := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  letI : Algebra.IsSeparable J (modularFunctionFieldCoeff N K) := isSeparable_coeff_field N K
  have hres := (coeff_place_residue_algebraMap_bijective N K w).surjective
  have hbase : Function.Bijective (algebraMap K (w.restrict J).ResidueField) :=
    ⟨(algebraMap K (w.restrict J).ResidueField).injective,
      w.residue_algebraMap_surjective_restrict (F := J) hres⟩
  refine fun g => ?_
  exact (w.restrict J).completionTraceSum hbase
    (coeff_place_residue_algebraMap_bijective N K) g

end Dubon2026.SourceFunctionField
