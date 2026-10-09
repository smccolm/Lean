import Dubon2026.AdelicGoodActionBound
import Dubon2026.AdelicRestrictedTensorDirectLimit

/-! # The genuine finite-stage recipe for the full original adelic action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- Enlarge the actual tensor stage, apply the original local and fixed-base representations, then include the result in the genuine directed quotient. -/
def adelicRestrictedActionOnStage (a : RationalAdelicGL2) (n : ℕ) :
    adelicRestrictedStage F.toCuspForm n →ₗ[ℂ] AdelicRestrictedAlgebraicTensor F :=
  let m := adelicActionStage N a n
  (adelicRestrictedTensorOf F m).toLinearMap.comp
    ((adelicRestrictedFiniteTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N m)
      (adelicFinitePlaceEvaluation (goodAdelicPlaceInitial N m) a, adelicBaseProjection N a)).comp
      (adelicRestrictedStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m (le_adelicActionStage N a n)).toLinearMap)

/-- The actual finite-stage recipe realizes exactly the full original adelic action on the original vector. -/
theorem adelicRestrictedActionOnStage_intertwines (a : RationalAdelicGL2) (n : ℕ)
    (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedActionOnStage F a n x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedStageIsometry F n x) := by
  let m := adelicActionStage N a n
  let y := adelicRestrictedStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m (le_adelicActionStage N a n) x
  have h₁ := adelicRestrictedAlgebraicTensorIsometry_of F m
    (adelicRestrictedFiniteTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N m)
      (adelicFinitePlaceEvaluation (goodAdelicPlaceInitial N m) a, adelicBaseProjection N a) y)
  have h₂ := adelicRestrictedFiniteTensor_full_intertwines (goodAdelicPlaceInitial N m)
    (goodAdelicPlaceInitial_injective N m) F (goodAdelicPlaceInitial_good N m) a (adelicActionStage_spec N a n) y
  have h₃ := adelicRestrictedStageIsometry_map F n m (le_adelicActionStage N a n) x
  exact h₁.trans (h₂.trans (congrArg (adelicCyclicHilbertRepresentation F.toCuspForm a) h₃))

/-- The genuine finite-stage action recipe is compatible with every actual original unit-reference transition. -/
theorem adelicRestrictedActionOnStage_compatible (a : RationalAdelicGL2) (n m : ℕ) (h : n ≤ m)
    (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedActionOnStage F a m
      (adelicRestrictedStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicRestrictedActionOnStage F a n x := by
  apply (adelicRestrictedAlgebraicTensorIsometry F).injective
  rw [adelicRestrictedActionOnStage_intertwines, adelicRestrictedActionOnStage_intertwines,
    adelicRestrictedStageIsometry_map]

end
end Dubon2026
