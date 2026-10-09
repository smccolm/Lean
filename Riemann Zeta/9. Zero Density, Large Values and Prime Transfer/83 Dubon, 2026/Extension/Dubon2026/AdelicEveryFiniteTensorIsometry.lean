import Dubon2026.AdelicEveryFiniteTupleGram
import Dubon2026.AdelicFiniteTensorIsometry

/-! # Genuine finite tensor isometry including every original bad place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix
open scoped TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}

variable (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- The true finite Hilbert tensor Gram matrix is exactly the original full adelic unit-reference Gram matrix. -/
theorem adelicEveryFiniteFullTensorFamily_gram (hk : 0 < k)
    (a b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ (adelicFiniteFullTensorFamily F.toCuspForm v a) (adelicFiniteFullTensorFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteFullMixedFamily F.toCuspForm v hv a) (adelicFiniteFullMixedFamily F.toCuspForm v hv b) := by
  have ht := finiteHilbertPureTensor_inner (fun i => adelicLocalInnerCarrier F.toCuspForm (v i))
    (fun i => adelicLocalUnitOrbit F.toCuspForm (v i) (a.1 i))
    (fun i => adelicLocalUnitOrbit F.toCuspForm (v i) (b.1 i))
  have hg := adelicCyclicUnitReference_every_finiteFamily_gram v hv F hk a b
  exact (congrArg (fun c : ℂ => c * inner ℂ
    (adelicFiniteFamilyAwayOrbit F.toCuspForm v a.2) (adelicFiniteFamilyAwayOrbit F.toCuspForm v b.2)) ht).trans hg.symm

/-- The genuine finite local/full-complement algebraic Hilbert tensor maps isometrically into the original full adelic Hilbert representation. -/
def adelicEveryFiniteFullTensorIsometry (hk : 0 < k) :
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) →ₗᵢ[ℂ]
      AdelicCyclicHilbert F.toCuspForm :=
  @gramSpanningIsometry
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorFamily F.toCuspForm v) (adelicFiniteFullMixedFamily F.toCuspForm v hv)
    (adelicEveryFiniteFullTensorFamily_gram F v hv hk)
    (adelicFiniteFullTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))

/-- Every actual finite pure orbit tensor maps to exactly its original full adelic mixed orbit vector. -/
theorem adelicEveryFiniteFullTensorIsometry_family (hk : 0 < k)
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicEveryFiniteFullTensorIsometry F v hv hk (adelicFiniteFullTensorFamily F.toCuspForm v a) =
      adelicFiniteFullMixedFamily F.toCuspForm v hv a :=
  gramSpanningIsometry_family _ _ _ _ a

end
end Dubon2026
