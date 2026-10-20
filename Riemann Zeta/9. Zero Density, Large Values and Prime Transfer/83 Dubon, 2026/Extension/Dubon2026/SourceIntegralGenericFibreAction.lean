import Dubon2026.SourceIntegralGenericFibre
import Dubon2026.SourceCoefficientGroupAction

/-! Exact representation compatibility of the original integral generic fibre.
The tensor comparison intertwines the literal scalar extension of each
original integral group operator with that same matrix over the field.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

universe u
variable (R K : Type u) [CommRing R] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K]
variable {m : ℕ} (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)

/-- The original generic-fibre equivalence intertwines the actual integral group action after literal tensor scalar extension. -/
theorem sourceIntegralGenericFibreEquiv_action
    (g : Matrix.GeneralLinearGroup (Fin (m + 1)) R)
    (z : K ⊗[R] generalLinearIntegralInducedSubmodule R (m + 1) weight) :
    sourceIntegralGenericFibreEquiv R K weight hw
      ((generalLinearIntegralInducedRepresentation R (m + 1) weight g).baseChange K z) =
      generalLinearIntegralInducedRepresentation K (m + 1) weight
        (Matrix.GeneralLinearGroup.map (algebraMap R K) g)
          (sourceIntegralGenericFibreEquiv R K weight hw z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul k p =>
    rw [LinearMap.baseChange_tmul, sourceIntegralGenericFibreEquiv_tmul,
      sourceIntegralGenericFibreEquiv_tmul, map_smul, sourceInducedCoefficientMap_action]
  | add z w hz hw' => simp only [map_add, hz, hw']

/-- The generic-fibre equivalence carries the same normalized integral highest vector to the normalized highest vector in the original field representation. -/
theorem sourceIntegralGenericFibreEquiv_highest :
    sourceIntegralGenericFibreEquiv R K weight hw
      ((1 : K) ⊗ₜ[R] integralDominantHighestVector R weight hw) =
        integralDominantHighestVector K weight hw := by
  rw [sourceIntegralGenericFibreEquiv_tmul, one_smul, sourceInducedCoefficientMap_highest]

end
end Dubon2026
