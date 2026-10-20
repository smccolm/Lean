import Dubon2026.SourceCoefficientSpan
import Dubon2026.SourceFractionTensorInjective

/-! Identification of the actual integral coefficient generic fibre.
The actual coefficient image contains the normalized highest vector and is
stable under the actual Lie action. Highest-vector generation proves its
field span is the entire original induction. Native fraction localization
then gives injectivity of the literal tensor map.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

universe u
variable (R K : Type u) [CommRing R] [Field K] [CharZero K] [Algebra R K]
variable {m : ℕ} (weight : Fin (m + 1) → ℤ) (hw : Antitone weight)

include hw in
/-- The field span of the original integral induced coefficient module is the entire original induced module over the field. -/
theorem sourceInducedCoefficientMap_span :
    Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K (m + 1) weight) :
      Set (generalLinearIntegralInducedSubmodule K (m + 1) weight)) = ⊤ := by
  let W := sourceCoefficientSpanLieSubmodule R K (m + 1) weight
  have hv : integralDominantHighestVector K weight hw ∈ W := by
    change integralDominantHighestVector K weight hw ∈
      Submodule.span K (LinearMap.range (sourceInducedCoefficientMap R K (m + 1) weight))
    rw [← sourceInducedCoefficientMap_highest R K weight hw]
    exact Submodule.subset_span (LinearMap.mem_range_self _ _)
  have hs : LieSubmodule.lieSpan K (LieAlgebra.SpecialLinear.sl (Fin (m + 1)) K)
      {integralDominantHighestVector K weight hw} ≤ W := by
    apply LieSubmodule.lieSpan_le.mpr
    intro p hp
    rw [Set.mem_singleton_iff.mp hp]
    exact hv
  rw [sourceInduced_highest_lieSpan K weight hw] at hs
  exact congrArg LieSubmodule.toSubmodule (top_le_iff.mp hs)

include hw in
/-- The literal scalar-extension tensor of the original integral induction maps onto the entire original field induction. -/
theorem sourceInducedCoefficientMap_lift_surjective :
    Function.Surjective ((sourceInducedCoefficientMap R K (m + 1) weight).liftBaseChange K) := by
  rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange]
  exact sourceInducedCoefficientMap_span R K weight hw

variable [IsFractionRing R K]

/-- The original integral induced module has exactly the original field induction as its generic fibre, through its actual coefficient map. -/
def sourceIntegralGenericFibreEquiv :
    K ⊗[R] generalLinearIntegralInducedSubmodule R (m + 1) weight ≃ₗ[K]
      generalLinearIntegralInducedSubmodule K (m + 1) weight :=
  LinearEquiv.ofBijective
    ((sourceInducedCoefficientMap R K (m + 1) weight).liftBaseChange K)
    ⟨sourceFraction_liftBaseChange_injective R K _
      (sourceInducedCoefficientMap_injective R K (m + 1)
        (IsFractionRing.injective R K) weight),
      sourceInducedCoefficientMap_lift_surjective R K weight hw⟩

/-- The generic-fibre identification preserves the exact original scalar and integral regular function on every pure tensor. -/
theorem sourceIntegralGenericFibreEquiv_tmul (k : K)
    (p : generalLinearIntegralInducedSubmodule R (m + 1) weight) :
    sourceIntegralGenericFibreEquiv R K weight hw (k ⊗ₜ[R] p) =
      k • sourceInducedCoefficientMap R K (m + 1) weight p := rfl

end
end Dubon2026
