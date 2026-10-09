import Dubon2026.AdelicSplitStageMaps
import Dubon2026.AdelicGoodActionBound

/-! # Independent external actions on the genuine good, bad and real tensor factors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The independent product representation on the actual good, bad and full real factors. -/
def adelicSplitStageRepresentation (n : ℕ) :
    Representation ℂ
      ((∀ i : Fin n, GeneralLinearGroup (Fin 2) ((goodAdelicPlaceInitial N n i).adicCompletion ℚ)) ×
        (AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ)) (adelicSplitStage f n) :=
  Representation.tprod
    ((adelicFiniteLocalTensorRepresentation f (goodAdelicPlaceInitial N n)).comp (MonoidHom.fst _ _))
    ((adelicFiniteRealTensorRepresentation f (adelicBadPlaceFamily N)).comp (MonoidHom.snd _ _))

variable (F : PrimitiveCuspForm N k)

/-- The proved base factorization intertwines the independent original good, bad and real actions. -/
theorem adelicSplitStageEquiv_intertwines (hk : 0 < k) (n : ℕ)
    (a : (∀ i : Fin n, GeneralLinearGroup (Fin 2) ((goodAdelicPlaceInitial N n i).adicCompletion ℚ)) ×
      (AdelicBadLocalTuple N × GeneralLinearGroup (Fin 2) ℝ))
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageEquiv F hk n (adelicSplitStageRepresentation F.toCuspForm n a x) =
      adelicRestrictedFiniteTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N n)
        (a.1, adelicBadRealBaseEquiv N a.2) (adelicSplitStageEquiv F hk n x) := by
  let L := (adelicSplitStageEquiv F hk n).toLinearMap.comp
    (adelicSplitStageRepresentation F.toCuspForm n a)
  let R := (adelicRestrictedFiniteTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N n)
      (a.1, adelicBadRealBaseEquiv N a.2)).comp (adelicSplitStageEquiv F hk n).toLinearMap
  change L x = R x
  induction x using TensorProduct.induction_on with
  | zero => exact L.map_zero.trans R.map_zero.symm
  | tmul x y =>
    change TensorProduct.map LinearMap.id (adelicBadRealTensorBaseEquiv F hk).toLinearMap
        (TensorProduct.map (adelicFiniteLocalTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N n) a.1)
          (adelicFiniteRealTensorRepresentation F.toCuspForm (adelicBadPlaceFamily N) a.2) (x ⊗ₜ[ℂ] y)) =
      TensorProduct.map (adelicFiniteLocalTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N n) a.1)
        (adelicRestrictedBaseCoreRepresentation F.toCuspForm (adelicBadRealBaseEquiv N a.2))
        (TensorProduct.map LinearMap.id (adelicBadRealTensorBaseEquiv F hk).toLinearMap (x ⊗ₜ[ℂ] y))
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    exact congrArg (fun z =>
      adelicFiniteLocalTensorRepresentation F.toCuspForm (goodAdelicPlaceInitial N n) a.1 x ⊗ₜ[ℂ] z)
      (adelicBadRealTensorBaseEquiv_intertwines F hk a.2 y)
  | add x y hx hy => exact (L.map_add x y).trans ((congrArg₂ (· + ·) hx hy).trans (R.map_add x y).symm)

/-- The independent split action uses precisely the actual selected good coordinates and original bad/real coordinates. -/
def adelicSplitStageFullOperator (n : ℕ) (a : RationalAdelicGL2) :
    Module.End ℂ (adelicSplitStage F.toCuspForm n) :=
  adelicSplitStageRepresentation F.toCuspForm n
    (adelicFinitePlaceEvaluation (goodAdelicPlaceInitial N n) a,
      (adelicBadRealBaseEquiv N).symm (adelicBaseProjection N a))

/-- Once the genuine good tail is in local level, the independent fully split action realizes the full original adelic action. -/
theorem adelicSplitStageFullOperator_intertwines (hk : 0 < k) (n : ℕ) (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin n, w ≠ goodAdelicPlaceInitial N n i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitStageIsometry F hk n (adelicSplitStageFullOperator F n a x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicSplitStageIsometry F hk n x) := by
  have he := adelicSplitStageEquiv_intertwines F hk n
    (adelicFinitePlaceEvaluation (goodAdelicPlaceInitial N n) a,
      (adelicBadRealBaseEquiv N).symm (adelicBaseProjection N a)) x
  rw [(adelicBadRealBaseEquiv N).apply_symm_apply] at he
  exact (congrArg (adelicRestrictedStageIsometry F n) he).trans
    (adelicRestrictedFiniteTensor_full_intertwines (goodAdelicPlaceInitial N n)
      (goodAdelicPlaceInitial_injective N n) F (goodAdelicPlaceInitial_good N n) a ha
      (adelicSplitStageEquiv F hk n x))

end
end Dubon2026
