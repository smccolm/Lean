import Dubon2026.AdelicRestrictedTensorBase
import Dubon2026.AdelicFiniteTensorIsometry

/-! # Genuine finite good-place tensors with one fixed original real-and-bad-place factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)

/-- The actual finite good-place tensor paired with the same original fixed base, independent of the selected family. -/
abbrev AdelicRestrictedFiniteTensor := AdelicFiniteLocalTensor f v ⊗[ℂ] adelicRestrictedBaseCore f

/-- The genuine finite tensor with fixed base has its original product Hilbert norm. -/
instance adelicRestrictedFiniteTensorNormed : NormedAddCommGroup (AdelicRestrictedFiniteTensor f v) :=
  @TensorProduct.instNormedAddCommGroup ℂ (AdelicFiniteLocalTensor f v) (adelicRestrictedBaseCore f)
    inferInstance inferInstance inferInstance inferInstance (adelicRestrictedBaseCoreInner f)

/-- The genuine finite tensor with fixed base has the original product inner product. -/
instance adelicRestrictedFiniteTensorInner : InnerProductSpace ℂ (AdelicRestrictedFiniteTensor f v) :=
  @TensorProduct.instInnerProductSpace ℂ (AdelicFiniteLocalTensor f v) (adelicRestrictedBaseCore f)
    inferInstance inferInstance inferInstance inferInstance (adelicRestrictedBaseCoreInner f)

/-- The original pure orbit family combines actual selected local orbit vectors with the fixed original base orbit. -/
def adelicRestrictedFiniteTensorFamily
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    AdelicRestrictedFiniteTensor f v :=
  adelicFiniteLocalTensorFamily f v b.1 ⊗ₜ[ℂ] adelicRestrictedBaseOrbit f b.2

/-- The genuine original fixed-base orbit tensors span the whole actual finite tensor. -/
theorem adelicRestrictedFiniteTensorFamily_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicRestrictedFiniteTensorFamily f v)) = ⊤ :=
  @tensorFamily_span_eq_top
    (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) (adelicRestrictedBaseGroup N)
    (AdelicFiniteLocalTensor f v) (adelicRestrictedBaseCore f)
    inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteLocalTensorFamily f v) (adelicRestrictedBaseOrbit f)
    (adelicFiniteLocalTensorFamily_span f v hf) (adelicRestrictedBaseOrbit_span f)

/-- The literal fixed-base inclusion defines a genuine tensor isometry into the actual selected-place full-complement tensor. -/
def adelicRestrictedFiniteTensorInclusion (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    AdelicRestrictedFiniteTensor f v →ₗᵢ[ℂ] (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  @TensorProduct.mapIsometry ℂ (AdelicFiniteLocalTensor f v) (adelicRestrictedBaseCore f)
    (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicRestrictedBaseCoreInner f)
    inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    LinearIsometry.id (adelicRestrictedBaseCoreInclusion f v hgood)

/-- Every original fixed-base pure tensor is included with the identical actual adelic orbit coordinates. -/
theorem adelicRestrictedFiniteTensorInclusion_family (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedFiniteTensorInclusion f v hgood (adelicRestrictedFiniteTensorFamily f v b) =
      adelicFiniteFullTensorFamily f v (b.1, adelicRestrictedBaseToFiniteAway v hgood b.2) := by
  change TensorProduct.map LinearMap.id (adelicRestrictedBaseCoreInclusion f v hgood).toLinearMap
    (adelicFiniteLocalTensorFamily f v b.1 ⊗ₜ[ℂ] adelicRestrictedBaseOrbit f b.2) = _
  rw [TensorProduct.map_tmul]
  exact congrArg (fun x => adelicFiniteLocalTensorFamily f v b.1 ⊗ₜ[ℂ] x)
    (adelicRestrictedBaseCoreInclusion_orbit f v hgood b.2)

variable (F : PrimitiveCuspForm N k)

/-- Each genuine finite good-place/fixed-base tensor maps isometrically into the original adelic cusp Hilbert space. -/
def adelicRestrictedFiniteTensorIsometry (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    AdelicRestrictedFiniteTensor F.toCuspForm v →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  (adelicFiniteFullTensorIsometry F v hv hgood).comp (adelicRestrictedFiniteTensorInclusion F.toCuspForm v hgood)

/-- The genuine fixed-base finite tensor isometry realizes exactly the original local product and original base matrix. -/
theorem adelicRestrictedFiniteTensorIsometry_family (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedFiniteTensorIsometry v F hv hgood (adelicRestrictedFiniteTensorFamily F.toCuspForm v b) =
      adelicCyclicHilbertRepresentation F.toCuspForm (adelicFinitePlaceProduct v hv b.1 * b.2.val)
        (adelicCyclicUnitReference F.toCuspForm) := by
  have h₁ := congrArg (adelicFiniteFullTensorIsometry F v hv hgood)
    (adelicRestrictedFiniteTensorInclusion_family F.toCuspForm v hgood b)
  have h₂ := adelicFiniteFullTensorIsometry_family F v hv hgood
    (b.1, adelicRestrictedBaseToFiniteAway v hgood b.2)
  exact h₁.trans h₂

end
end Dubon2026
