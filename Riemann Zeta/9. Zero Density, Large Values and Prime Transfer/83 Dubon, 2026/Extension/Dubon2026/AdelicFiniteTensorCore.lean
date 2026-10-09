import Dubon2026.FiniteHilbertTensor
import Dubon2026.AdelicLocalUnitOrbit
import Dubon2026.AdelicFiniteTupleGram

/-! # Actual finite local Hilbert tensors and their genuine full complementary orbit core -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Bundle the original local algebraic core with its actual inherited Hilbert inner product. -/
def adelicLocalInnerCarrier (v : HeightOneSpectrum ℤ) : ComplexInnerCarrier :=
  @ComplexInnerCarrier.of (adelicLocalCyclicCore f v) inferInstance (adelicLocalCyclicCoreInnerProduct f v)

variable {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ)

/-- The genuine finite algebraic Hilbert tensor of the original local cyclic cores. -/
abbrev AdelicFiniteLocalTensor := finiteHilbertTensor n (fun i => adelicLocalInnerCarrier f (v i))

/-- The actual finite pure tensor of normalized original local cusp orbit vectors. -/
def adelicFiniteLocalTensorFamily
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) : AdelicFiniteLocalTensor f v :=
  finiteHilbertPureTensor (fun i => adelicLocalInnerCarrier f (v i)) (fun i => adelicLocalUnitOrbit f (v i) (g i))

/-- The genuine finite local pure orbit family spans the entire original finite tensor. -/
theorem adelicFiniteLocalTensorFamily_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteLocalTensorFamily f v)) = ⊤ :=
  finiteHilbertPureTensor_family_span (fun i => adelicLocalInnerCarrier f (v i))
    (fun i => GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (fun i => adelicLocalUnitOrbit f (v i)) (fun i => adelicLocalUnitOrbit_span f hf (v i))

/-- The actual full remaining-coordinate action is the original adelic representation restricted to its genuine coordinate kernel. -/
def adelicFiniteFamilyAwayRepresentation : Representation ℂ (adelicFiniteFamilyAwayGroup v) (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp (adelicFiniteFamilyAwayGroup v).subtype

/-- The full complementary core is the actual orbit span of the original unit reference under the genuine remaining-coordinate subgroup. -/
def adelicFiniteFamilyAwayCore : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun a : adelicFiniteFamilyAwayGroup v =>
    adelicFiniteFamilyAwayRepresentation f v a (adelicCyclicUnitReference f)))

/-- The genuine full complementary algebraic core inherits the original Hilbert inner product. -/
instance adelicFiniteFamilyAwayCoreInner : InnerProductSpace ℂ (adelicFiniteFamilyAwayCore f v) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicFiniteFamilyAwayCore f v)

/-- The original full complementary normalized cusp orbit, viewed in its genuine algebraic span. -/
def adelicFiniteFamilyAwayOrbit (a : adelicFiniteFamilyAwayGroup v) : adelicFiniteFamilyAwayCore f v :=
  ⟨adelicFiniteFamilyAwayRepresentation f v a (adelicCyclicUnitReference f), Submodule.subset_span ⟨a, rfl⟩⟩

/-- The genuine complementary orbit family spans exactly its original full complementary core. -/
theorem adelicFiniteFamilyAwayOrbit_span :
    Submodule.span ℂ (Set.range (adelicFiniteFamilyAwayOrbit f v)) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff (adelicFiniteFamilyAwayCore f v) _).mpr rfl

/-- The genuine finite local tensor paired with the full remaining-coordinate orbit core has its actual Hilbert tensor norm. -/
instance adelicFiniteFullTensorNormed :
    NormedAddCommGroup (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  @TensorProduct.instNormedAddCommGroup ℂ (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)

/-- The actual finite local/full-complement tensor carries the product of its genuine original inner products. -/
instance adelicFiniteFullTensorInner :
    InnerProductSpace ℂ (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  @TensorProduct.instInnerProductSpace ℂ (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)

/-- The genuine pure mixed orbit family in the actual finite local/full-complement tensor. -/
def adelicFiniteFullTensorFamily
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v :=
  adelicFiniteLocalTensorFamily f v b.1 ⊗ₜ[ℂ] adelicFiniteFamilyAwayOrbit f v b.2

/-- The original mixed orbit family spans the entire genuine finite local/full-complement algebraic tensor. -/
theorem adelicFiniteFullTensorFamily_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteFullTensorFamily f v)) = ⊤ :=
  @tensorFamily_span_eq_top
    (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) (adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteLocalTensorFamily f v) (adelicFiniteFamilyAwayOrbit f v)
    (adelicFiniteLocalTensorFamily_span f v hf) (adelicFiniteFamilyAwayOrbit_span f v)

end
end Dubon2026
