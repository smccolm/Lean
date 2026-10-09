import Dubon2026.AdelicRestrictedTensorChain
import Dubon2026.SequentialHilbertLimitRealization

/-! # The genuine restricted algebraic tensor and its original isometric realization -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The actual directed quotient of all genuine good-place finite tensors, with original unit references and a fixed original base. -/
abbrev AdelicRestrictedAlgebraicTensor :=
  SequentialHilbertLimit (adelicRestrictedStage F.toCuspForm)
    (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))

/-- The actual finite-stage inclusion into the original restricted algebraic tensor quotient. -/
def adelicRestrictedTensorOf (n : ℕ) :
    adelicRestrictedStage F.toCuspForm n →ₗᵢ[ℂ] AdelicRestrictedAlgebraicTensor F :=
  sequentialHilbertOfIsometry (adelicRestrictedStage F.toCuspForm)
    (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F)) n

/-- The genuine restricted algebraic tensor maps isometrically to the original adelic Hilbert space. -/
def adelicRestrictedAlgebraicTensorIsometry :
    AdelicRestrictedAlgebraicTensor F →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  @sequentialHilbertLimitIsometry (adelicRestrictedStage F.toCuspForm)
    (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicRestrictedStageIsometry F) (adelicRestrictedStageIsometry_step F)

/-- Every genuine finite tensor retains exactly its original adelic realization in the directed quotient. -/
theorem adelicRestrictedAlgebraicTensorIsometry_of (n : ℕ) (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedAlgebraicTensorIsometry F (adelicRestrictedTensorOf F n x) =
      adelicRestrictedStageIsometry F n x := rfl

/-- Every genuine restricted algebraic tensor is represented at a finite original stage. -/
theorem adelicRestrictedTensor_exists_stage (x : AdelicRestrictedAlgebraicTensor F) :
    ∃ n y, adelicRestrictedTensorOf F n y = x :=
  sequentialHilbertLimit_exists_stage (adelicRestrictedStage F.toCuspForm)
    (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F)) x

/-- The actual restricted tensor range consists exactly of the original finite-stage ranges. -/
theorem adelicRestrictedAlgebraicTensorIsometry_mem_range_iff (y : AdelicCyclicHilbert F.toCuspForm) :
    y ∈ (adelicRestrictedAlgebraicTensorIsometry F).toLinearMap.range ↔
      ∃ n x, adelicRestrictedStageIsometry F n x = y :=
  @sequentialHilbertLimitIsometry_mem_range_iff (adelicRestrictedStage F.toCuspForm)
    (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicRestrictedStageIsometry F) (adelicRestrictedStageIsometry_step F) y

end
end Dubon2026
