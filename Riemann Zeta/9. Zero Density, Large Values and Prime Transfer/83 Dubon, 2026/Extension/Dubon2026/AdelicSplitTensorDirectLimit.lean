import Dubon2026.AdelicSplitTensorChain
import Dubon2026.SequentialHilbertLimitRealization

/-! # The actual directed quotient of fully split finite and real tensor factors -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The genuine restricted algebraic tensor of all original finite local cores and the full real core. -/
abbrev AdelicSplitAlgebraicTensor :=
  SequentialHilbertLimit (adelicSplitStage F.toCuspForm)
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))

/-- Each independent finite tensor includes isometrically into the actual directed quotient. -/
def adelicSplitTensorOf (n : ℕ) :
    adelicSplitStage F.toCuspForm n →ₗᵢ[ℂ] AdelicSplitAlgebraicTensor F :=
  sequentialHilbertOfIsometry (adelicSplitStage F.toCuspForm)
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F)) n

/-- The fully split restricted tensor realizes the original cusp representation with its independently descended norm. -/
def adelicSplitAlgebraicTensorIsometry (hk : 0 < k) :
    AdelicSplitAlgebraicTensor F →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  @sequentialHilbertLimitIsometry (adelicSplitStage F.toCuspForm)
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicSplitStageIsometry F hk) (adelicSplitStageIsometry_step F hk)

/-- Every fully split finite tensor retains exactly its original adelic vector in the directed quotient. -/
theorem adelicSplitAlgebraicTensorIsometry_of (hk : 0 < k) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitAlgebraicTensorIsometry F hk (adelicSplitTensorOf F n x) =
      adelicSplitStageIsometry F hk n x := rfl

/-- Every tensor in the genuine full restricted algebraic product has an actual finite-stage representative. -/
theorem adelicSplitTensor_exists_stage (x : AdelicSplitAlgebraicTensor F) :
    ∃ n y, adelicSplitTensorOf F n y = x :=
  sequentialHilbertLimit_exists_stage (adelicSplitStage F.toCuspForm)
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F)) x

/-- The realized fully split restricted tensor consists precisely of its original finite-stage images. -/
theorem adelicSplitAlgebraicTensorIsometry_mem_range_iff (hk : 0 < k)
    (y : AdelicCyclicHilbert F.toCuspForm) :
    y ∈ (adelicSplitAlgebraicTensorIsometry F hk).toLinearMap.range ↔
      ∃ n x, adelicSplitStageIsometry F hk n x = y :=
  @sequentialHilbertLimitIsometry_mem_range_iff (adelicSplitStage F.toCuspForm)
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicSplitStageIsometry F hk) (adelicSplitStageIsometry_step F hk) y

end
end Dubon2026
