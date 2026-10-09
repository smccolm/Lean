import Dubon2026.AdelicEveryFiniteTensorIsometry
import Dubon2026.AdelicRealFiniteTensor
import Dubon2026.AdelicRealFinitePlaceCoordinates

/-! # Genuine selected finite local factors tensored with the original full real factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)

/-- The genuine finite tensor of selected original local cores paired with the original full real core. -/
abbrev AdelicFiniteRealTensor := AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFullRealUnitCore f

/-- The genuine selected finite/real tensor has its independent original product Hilbert norm. -/
instance adelicFiniteRealTensorNormed : NormedAddCommGroup (AdelicFiniteRealTensor f v) :=
  @TensorProduct.instNormedAddCommGroup ℂ (AdelicFiniteLocalTensor f v) (adelicFullRealUnitCore f)
    inferInstance inferInstance inferInstance inferInstance (adelicFullRealUnitCoreInner f)

/-- The genuine selected finite/real tensor has its independent original product inner product. -/
instance adelicFiniteRealTensorInner : InnerProductSpace ℂ (AdelicFiniteRealTensor f v) :=
  @TensorProduct.instInnerProductSpace ℂ (AdelicFiniteLocalTensor f v) (adelicFullRealUnitCore f)
    inferInstance inferInstance inferInstance inferInstance (adelicFullRealUnitCoreInner f)

/-- The actual original selected local orbit tuple and real orbit as a genuine pure tensor. -/
def adelicFiniteRealTensorFamily
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    AdelicFiniteRealTensor f v :=
  adelicFiniteLocalTensorFamily f v a.1 ⊗ₜ[ℂ] adelicFullRealUnitOrbit f a.2

/-- The literal original mixed orbit under the genuine selected finite and full real group product. -/
def adelicFiniteRealMixedFamily (hv : Function.Injective v)
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    AdelicCyclicHilbert f :=
  adelicCyclicHilbertRepresentation f (adelicFiniteRealJointHom v hv a) (adelicCyclicUnitReference f)

/-- The original pure orbit tensors span the entire genuine selected finite/real tensor. -/
theorem adelicFiniteRealTensorFamily_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteRealTensorFamily f v)) = ⊤ :=
  @tensorFamily_span_eq_top (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (GeneralLinearGroup (Fin 2) ℝ) (AdelicFiniteLocalTensor f v) (adelicFullRealUnitCore f)
    inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteLocalTensorFamily f v) (adelicFullRealUnitOrbit f)
    (adelicFiniteLocalTensorFamily_span f v hf) (adelicFullRealUnitOrbit_span f)

variable (F : PrimitiveCuspForm N k) (hv : Function.Injective v)

/-- The actual all-place original Gram identity gives precisely the independent selected finite/real tensor inner product. -/
theorem adelicFiniteRealTensorFamily_gram (hk : 0 < k)
    (a b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    inner ℂ (adelicFiniteRealTensorFamily F.toCuspForm v a) (adelicFiniteRealTensorFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteRealMixedFamily F.toCuspForm v hv a) (adelicFiniteRealMixedFamily F.toCuspForm v hv b) := by
  have ht := finiteHilbertPureTensor_inner (fun i => adelicLocalInnerCarrier F.toCuspForm (v i))
    (fun i => adelicLocalUnitOrbit F.toCuspForm (v i) (a.1 i))
    (fun i => adelicLocalUnitOrbit F.toCuspForm (v i) (b.1 i))
  have hg := adelicCyclicUnitReference_every_finiteFamily_gram v hv F hk
    (a.1, adelicRealToFiniteAway v a.2) (b.1, adelicRealToFiniteAway v b.2)
  exact (congrArg (fun c : ℂ => c * inner ℂ (adelicFullRealUnitOrbit F.toCuspForm a.2)
    (adelicFullRealUnitOrbit F.toCuspForm b.2)) ht).trans hg.symm

/-- The genuine tensor of selected original finite factors and full real factor maps isometrically into the original adelic Hilbert space. -/
def adelicFiniteRealTensorIsometry (hk : 0 < k) :
    AdelicFiniteRealTensor F.toCuspForm v →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  gramSpanningIsometry (adelicFiniteRealTensorFamily F.toCuspForm v) (adelicFiniteRealMixedFamily F.toCuspForm v hv)
    (adelicFiniteRealTensorFamily_gram v F hv hk)
    (adelicFiniteRealTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))

/-- Every genuine finite/real pure tensor realizes the literal original mixed cusp orbit. -/
theorem adelicFiniteRealTensorIsometry_family (hk : 0 < k)
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    adelicFiniteRealTensorIsometry v F hv hk (adelicFiniteRealTensorFamily F.toCuspForm v a) =
      adelicFiniteRealMixedFamily F.toCuspForm v hv a :=
  gramSpanningIsometry_family _ _ _ _ a

end
end Dubon2026
