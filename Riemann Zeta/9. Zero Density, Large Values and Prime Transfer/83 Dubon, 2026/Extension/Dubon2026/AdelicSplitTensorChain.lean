import Dubon2026.AdelicBadRealBaseEquivariance
import Dubon2026.AdelicRestrictedTensorChain

/-! # Restricted stages with every bad local factor and the full real factor explicitly split -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The independent finite product of the original good, bad and full real factors. -/
def adelicSplitStage (n : ℕ) : ComplexInnerCarrier :=
  (ComplexInnerCarrier.of (AdelicFiniteLocalTensor f (goodAdelicPlaceInitial N n))).tensor
    (ComplexInnerCarrier.of (AdelicFiniteRealTensor f (adelicBadPlaceFamily N)))

/-- The actual next good-place unit insertion, retaining all individual bad and real factors. -/
def adelicSplitStageStep (hf : f ≠ 0) (n : ℕ) :
    adelicSplitStage f n →ₗᵢ[ℂ] adelicSplitStage f (n + 1) :=
  TensorProduct.mapIsometry
    (adelicFiniteLocalReferenceExtension f hf (goodAdelicPlaceInitial N (n + 1))) LinearIsometry.id

variable (F : PrimitiveCuspForm N k)

/-- The proved original bad/real factorization identifies each independent split stage with the original base stage. -/
def adelicSplitStageEquiv (hk : 0 < k) (n : ℕ) :
    adelicSplitStage F.toCuspForm n ≃ₗᵢ[ℂ] adelicRestrictedStage F.toCuspForm n :=
  @TensorProduct.congrIsometry ℂ
    (AdelicFiniteLocalTensor F.toCuspForm (goodAdelicPlaceInitial N n))
    (AdelicFiniteRealTensor F.toCuspForm (adelicBadPlaceFamily N))
    (AdelicFiniteLocalTensor F.toCuspForm (goodAdelicPlaceInitial N n))
    (adelicRestrictedBaseCore F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance (adelicRestrictedBaseCoreInner F.toCuspForm)
    (LinearIsometryEquiv.refl ℂ _)
    (adelicBadRealTensorBaseEquiv F hk)

/-- Factorization of the fixed base commutes with the actual next good-place reference insertion. -/
theorem adelicSplitStageEquiv_step (hk : 0 < k) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageEquiv F hk (n + 1)
      (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n x) =
      adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n
        (adelicSplitStageEquiv F hk n x) := by
  let L := (adelicSplitStageEquiv F hk (n + 1)).toLinearMap.comp
    (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n).toLinearMap
  let R := (adelicRestrictedStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n).toLinearMap.comp
    (adelicSplitStageEquiv F hk n).toLinearMap
  change L x = R x
  induction x using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans R.map_zero.symm
  | tmul x y =>
    change TensorProduct.map LinearMap.id (adelicBadRealTensorBaseEquiv F hk).toLinearMap
        (TensorProduct.map
          (adelicFiniteLocalReferenceExtension F.toCuspForm (primitiveCuspForm_ne_zero F)
            (goodAdelicPlaceInitial N (n + 1))).toLinearMap LinearMap.id (x ⊗ₜ[ℂ] y)) =
      TensorProduct.map
        (adelicFiniteLocalReferenceExtension F.toCuspForm (primitiveCuspForm_ne_zero F)
          (goodAdelicPlaceInitial N (n + 1))).toLinearMap LinearMap.id
        (TensorProduct.map LinearMap.id (adelicBadRealTensorBaseEquiv F hk).toLinearMap (x ⊗ₜ[ℂ] y))
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  | add x y hx hy => exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

/-- The original adelic realization of a tensor with all its finite and real factors explicitly separated. -/
def adelicSplitStageIsometry (hk : 0 < k) (n : ℕ) :
    adelicSplitStage F.toCuspForm n →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  (adelicRestrictedStageIsometry F n).comp (adelicSplitStageEquiv F hk n).toLinearIsometry

/-- Original realization is unchanged by the true reference insertion on fully split factors. -/
theorem adelicSplitStageIsometry_step (hk : 0 < k) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageIsometry F hk (n + 1)
      (adelicSplitStageStep F.toCuspForm (primitiveCuspForm_ne_zero F) n x) =
      adelicSplitStageIsometry F hk n x :=
  (congrArg (adelicRestrictedStageIsometry F (n + 1))
    (adelicSplitStageEquiv_step F hk n x)).trans
    (adelicRestrictedStageIsometry_step F n (adelicSplitStageEquiv F hk n x))

end
end Dubon2026
