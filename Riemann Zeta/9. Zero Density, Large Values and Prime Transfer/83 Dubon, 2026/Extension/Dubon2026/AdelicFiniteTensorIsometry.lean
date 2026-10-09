import Dubon2026.AdelicFiniteTensorCore
import Dubon2026.GramSpanningIsometry

/-! # The genuine finite-family tensor isometry into the original full adelic cusp space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}

/-- The original full adelic unit-reference orbit in its genuine finite-family group coordinates. -/
def adelicFiniteFullMixedFamily (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    AdelicCyclicHilbert f :=
  adelicCyclicHilbertRepresentation f (adelicFiniteFamilyEquiv v hv b) (adelicCyclicUnitReference f)

variable (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- The true finite Hilbert tensor Gram matrix is exactly the original full adelic unit-reference Gram matrix. -/
theorem adelicFiniteFullTensorFamily_gram (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ (adelicFiniteFullTensorFamily F.toCuspForm v a) (adelicFiniteFullTensorFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteFullMixedFamily F.toCuspForm v hv a) (adelicFiniteFullMixedFamily F.toCuspForm v hv b) := by
  have ht := finiteHilbertPureTensor_inner (fun i => adelicLocalInnerCarrier F.toCuspForm (v i))
    (fun i => adelicLocalUnitOrbit F.toCuspForm (v i) (a.1 i))
    (fun i => adelicLocalUnitOrbit F.toCuspForm (v i) (b.1 i))
  have hg := adelicCyclicUnitReference_finiteFamily_gram v hv F hgood a b
  exact (congrArg (fun c : ℂ => c * inner ℂ
    (adelicFiniteFamilyAwayOrbit F.toCuspForm v a.2) (adelicFiniteFamilyAwayOrbit F.toCuspForm v b.2)) ht).trans hg.symm

/-- The genuine finite local/full-complement algebraic Hilbert tensor maps isometrically into the original full adelic Hilbert representation. -/
def adelicFiniteFullTensorIsometry (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) →ₗᵢ[ℂ]
      AdelicCyclicHilbert F.toCuspForm :=
  @gramSpanningIsometry
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorFamily F.toCuspForm v) (adelicFiniteFullMixedFamily F.toCuspForm v hv)
    (adelicFiniteFullTensorFamily_gram F v hv hgood)
    (adelicFiniteFullTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))

/-- Every actual finite pure orbit tensor maps to exactly its original full adelic mixed orbit vector. -/
theorem adelicFiniteFullTensorIsometry_family (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteFullTensorFamily F.toCuspForm v a) =
      adelicFiniteFullMixedFamily F.toCuspForm v hv a :=
  gramSpanningIsometry_family _ _ _ _ a

end
end Dubon2026
