import Dubon2026.AdelicSplitStageAction
import Dubon2026.AdelicSplitTensorDirectLimit

/-! # The full original adelic action from independent individual local tensor actions -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- Enlarge by original unit vectors, apply the independent good, bad and real actions, and include in the actual quotient. -/
def adelicSplitActionOnStage (a : RationalAdelicGL2) (n : ℕ) :
    adelicSplitStage F.toCuspForm n →ₗ[ℂ] AdelicSplitAlgebraicTensor F :=
  let m := adelicActionStage N a n
  (adelicSplitTensorOf F m).toLinearMap.comp
    ((adelicSplitStageFullOperator F m a).comp
      (adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m (le_adelicActionStage N a n)).toLinearMap)

/-- The independent individual-factor finite-stage action realizes the full original adelic action. -/
theorem adelicSplitActionOnStage_intertwines (hk : 0 < k) (a : RationalAdelicGL2) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitAlgebraicTensorIsometry F hk (adelicSplitActionOnStage F a n x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitStageIsometry F hk n x) := by
  let m := adelicActionStage N a n
  let y := adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m (le_adelicActionStage N a n) x
  have h₁ := adelicSplitAlgebraicTensorIsometry_of F hk m (adelicSplitStageFullOperator F m a y)
  have h₂ := adelicSplitStageFullOperator_intertwines F hk m a (adelicActionStage_spec N a n) y
  have h₃ := adelicSplitStageIsometry_map F hk n m (le_adelicActionStage N a n) x
  exact h₁.trans (h₂.trans (congrArg (adelicCyclicHilbertRepresentation F.toCuspForm a) h₃))

/-- The independently defined full local action recipe respects every genuine unit-reference transition. -/
theorem adelicSplitActionOnStage_compatible (hk : 0 < k) (a : RationalAdelicGL2)
    (n m : ℕ) (h : n ≤ m) (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitActionOnStage F a m
      (adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicSplitActionOnStage F a n x := by
  apply (adelicSplitAlgebraicTensorIsometry F hk).injective
  rw [adelicSplitActionOnStage_intertwines F hk, adelicSplitActionOnStage_intertwines F hk,
    adelicSplitStageIsometry_map]

end
end Dubon2026
