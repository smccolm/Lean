import Dubon2026.AdelicSplitTensorChain

/-! # The actual iterated unit-reference maps between fully split tensor stages -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Insert the genuine original unit references between any two fully split stages. -/
def adelicSplitStageMap (hf : f ≠ 0) (n m : ℕ) (h : n ≤ m) :
    adelicSplitStage f n →ₗᵢ[ℂ] adelicSplitStage f m :=
  sequentialHilbertMap (adelicSplitStage f) (adelicSplitStageStep f hf) n m h

/-- The actual reference insertions form the directed system used by the full local tensor. -/
instance adelicSplitStageDirectedSystem (hf : f ≠ 0) :
    DirectedSystem (fun n => adelicSplitStage f n)
      (fun n m h => (adelicSplitStageMap f hf n m h).toLinearMap) :=
  sequentialHilbertDirectedSystem (adelicSplitStage f) (adelicSplitStageStep f hf)

variable (F : PrimitiveCuspForm N k)

/-- All genuine reference insertions preserve the original fully split tensor realization. -/
theorem adelicSplitStageIsometry_map (hk : 0 < k) (n m : ℕ) (h : n ≤ m)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageIsometry F hk m
      (adelicSplitStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicSplitStageIsometry F hk n x :=
  @sequentialHilbertMap_realization (adelicSplitStage F.toCuspForm)
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicSplitStageIsometry F hk) (adelicSplitStageIsometry_step F hk) n m h x

end
end Dubon2026
