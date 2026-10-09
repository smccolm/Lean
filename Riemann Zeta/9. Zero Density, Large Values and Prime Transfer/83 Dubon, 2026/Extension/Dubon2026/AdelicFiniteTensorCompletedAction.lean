import Dubon2026.AdelicFiniteTensorAction
import Dubon2026.AdelicFiniteFamilyTopology
import Dubon2026.IsometricRepresentationCompletion

/-! # The completed genuine finite external tensor action is the original full adelic representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ)

/-- The genuine original finite external tensor action preserves the true Hilbert tensor norm. -/
theorem adelicFiniteFullTensorRepresentation_norm (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (x : AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) :
    ‖adelicFiniteFullTensorRepresentation F.toCuspForm v b x‖ = ‖x‖ :=
  @linearMap_norm_of_isometric_intertwiner
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorIsometry F v hv hgood) (adelicFiniteFullTensorRepresentation F.toCuspForm v b)
    (adelicFiniteFullJointRepresentation F.toCuspForm v hv b)
    (adelicFiniteFullTensorIsometry_intertwines v F hv hgood b)
    (adelicCyclicHilbertOperator_norm F.toCuspForm (adelicFiniteFamilyEquiv v hv b)) x

/-- The actual finite external tensor representation extends by its genuine norm-preserving operators to the Hilbert completion. -/
def adelicFiniteFullHilbertTensorRepresentation (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
      (AdelicFiniteFullHilbertTensor F.toCuspForm v) :=
  isometricRepresentationCompletion (adelicFiniteFullTensorRepresentation F.toCuspForm v)
    (adelicFiniteFullTensorRepresentation_norm F v hv hgood)

/-- The actual completed tensor action intertwines exactly with the original full adelic action on every Hilbert vector. -/
theorem adelicFiniteFullHilbertTensorIsometry_intertwines (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm v) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood
      (adelicFiniteFullHilbertTensorRepresentation F v hv hgood b x) =
      adelicFiniteFullJointRepresentation F.toCuspForm v hv b
        (adelicFiniteFullHilbertTensorIsometry F v hv hgood x) :=
  @isometricRepresentationCompletion_intertwines
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorRepresentation F.toCuspForm v)
    (adelicFiniteFullTensorRepresentation_norm F v hv hgood)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorIsometry F v hv hgood) b
    (adelicCyclicHilbertOperator F.toCuspForm (adelicFiniteFamilyEquiv v hv b))
    (adelicFiniteFullTensorIsometry_intertwines v F hv hgood b) x

/-- The genuine completed finite external tensor action is strongly continuous in the actual local and complementary product topology. -/
theorem adelicFiniteFullHilbertTensorRepresentation_stronglyContinuous (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm v) :
    Continuous (fun b => adelicFiniteFullHilbertTensorRepresentation F v hv hgood b x) :=
  @isometric_intertwiner_stronglyContinuous
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteFullHilbertTensor F.toCuspForm v) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fun b x => adelicFiniteFullHilbertTensorRepresentation F v hv hgood b x)
    (fun b x => adelicFiniteFullJointRepresentation F.toCuspForm v hv b x)
    (adelicFiniteFullHilbertTensorIsometry F v hv hgood)
    (adelicFiniteFullHilbertTensorIsometry_intertwines F v hv hgood)
    (fun y => (adelicCyclicHilbertRepresentation_stronglyContinuous F.toCuspForm y).comp
      (adelicFiniteFamilyEquiv_continuous v hv)) x

end
end Dubon2026
