import Dubon2026.AdelicGoodPlaceEnumeration
import Dubon2026.AdelicRestrictedReferenceExtension
import Dubon2026.SequentialHilbertIsometries

/-! # The genuine sequential system of all good-place tensors with a fixed original base -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original finite good-place tensor and the same fixed base, with its genuine product norm. -/
def adelicRestrictedStage (n : ℕ) : ComplexInnerCarrier :=
  @ComplexInnerCarrier.of (AdelicRestrictedFiniteTensor f (goodAdelicPlaceInitial N n))
    (adelicRestrictedFiniteTensorNormed f (goodAdelicPlaceInitial N n))
    (adelicRestrictedFiniteTensorInner f (goodAdelicPlaceInitial N n))

/-- The genuine consecutive transition inserts the original normalized cusp vector at the next good place. -/
def adelicRestrictedStageStep (hf : f ≠ 0) (n : ℕ) :
    adelicRestrictedStage f n →ₗᵢ[ℂ] adelicRestrictedStage f (n + 1) :=
  adelicRestrictedReferenceExtension f (goodAdelicPlaceInitial N (n + 1)) hf

/-- The actual iterated original unit-reference insertion between any two finite stages. -/
def adelicRestrictedStageMap (hf : f ≠ 0) (n m : ℕ) (h : n ≤ m) :
    adelicRestrictedStage f n →ₗᵢ[ℂ] adelicRestrictedStage f m :=
  sequentialHilbertMap (adelicRestrictedStage f) (adelicRestrictedStageStep f hf) n m h

/-- The genuine finite original tensor transitions have identity and composition, without a compatibility premise. -/
instance adelicRestrictedStageDirectedSystem (hf : f ≠ 0) :
    DirectedSystem (fun n => adelicRestrictedStage f n)
      (fun n m h => (adelicRestrictedStageMap f hf n m h).toLinearMap) :=
  sequentialHilbertDirectedSystem (adelicRestrictedStage f) (adelicRestrictedStageStep f hf)

variable (F : PrimitiveCuspForm N k)

/-- The original isometric realization of each actual finite initial tensor and the fixed base. -/
def adelicRestrictedStageIsometry (n : ℕ) :
    adelicRestrictedStage F.toCuspForm n →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  adelicRestrictedFiniteTensorIsometry (goodAdelicPlaceInitial N n) F
    (goodAdelicPlaceInitial_injective N n) (goodAdelicPlaceInitial_good N n)

/-- The actual finite-stage realization is compatible with the true next unit-reference insertion. -/
theorem adelicRestrictedStageIsometry_step (n : ℕ) (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedStageIsometry F (n + 1)
      (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n x) =
      adelicRestrictedStageIsometry F n x := by
  change adelicRestrictedFiniteTensorIsometry (goodAdelicPlaceInitial N (n + 1)) F
    (goodAdelicPlaceInitial_injective N (n + 1)) (goodAdelicPlaceInitial_good N (n + 1))
    (adelicRestrictedReferenceExtension F.toCuspForm (goodAdelicPlaceInitial N (n + 1))
      (primitiveCuspForm_ne_zero F) x) =
    adelicRestrictedFiniteTensorIsometry (goodAdelicPlaceInitial N n) F
      (goodAdelicPlaceInitial_injective N n) (goodAdelicPlaceInitial_good N n) x
  have he := adelicRestrictedFiniteTensorIsometry_reference_extension (goodAdelicPlaceInitial N (n + 1)) F
    (goodAdelicPlaceInitial_injective N (n + 1)) (goodAdelicPlaceInitial_good N (n + 1)) x
  simpa only [goodAdelicPlaceInitial, Fin.val_castSucc] using he

/-- Every iterated genuine unit-reference transition preserves the exact original adelic vector. -/
theorem adelicRestrictedStageIsometry_map (n m : ℕ) (h : n ≤ m) (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedStageIsometry F m
      (adelicRestrictedStageMap F.toCuspForm (primitiveCuspForm_ne_zero F) n m h x) =
      adelicRestrictedStageIsometry F n x :=
  @sequentialHilbertMap_realization (adelicRestrictedStage F.toCuspForm)
    (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicRestrictedStageIsometry F) (adelicRestrictedStageIsometry_step F) n m h x

end
end Dubon2026
