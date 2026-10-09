import Dubon2026.AdelicFiniteRealTensor
import Dubon2026.AdelicFiniteTensorAction
import Dubon2026.AdelicRealFiniteTensorAction

/-! # Genuine external selected finite and full real tensor actions -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)

/-- The independently constructed external action of the genuine selected local factors and original real core. -/
def adelicFiniteRealTensorRepresentation :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ)
      (AdelicFiniteRealTensor f v) :=
  Representation.tprod ((adelicFiniteLocalTensorRepresentation f v).comp (MonoidHom.fst _ _))
    ((adelicFullRealUnitCoreRepresentation f).comp (MonoidHom.snd _ _))

/-- The actual external selected finite/real tensor action multiplies the genuine original orbit coordinates. -/
theorem adelicFiniteRealTensorFamily_action
    (b a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    adelicFiniteRealTensorRepresentation f v b (adelicFiniteRealTensorFamily f v a) =
      adelicFiniteRealTensorFamily f v (b * a) := by
  change TensorProduct.map (adelicFiniteLocalTensorRepresentation f v b.1) (adelicFullRealUnitCoreRepresentation f b.2)
    (adelicFiniteLocalTensorFamily f v a.1 ⊗ₜ[ℂ] adelicFullRealUnitOrbit f a.2) = _
  rw [TensorProduct.map_tmul]
  exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) (adelicFiniteLocalTensorFamily_action f v b.1 a.1)
    (adelicFullRealUnitOrbit_action f b.2 a.2)

/-- The original adelic representation pulled back along the actual selected finite/real group homomorphism. -/
def adelicFiniteRealJointRepresentation (hv : Function.Injective v) :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ)
      (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp (adelicFiniteRealJointHom v hv)

/-- The literal original mixed orbit family transforms by genuine selected finite/real group multiplication. -/
theorem adelicFiniteRealMixedFamily_action (hv : Function.Injective v)
    (b a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    adelicFiniteRealJointRepresentation f v hv b (adelicFiniteRealMixedFamily f v hv a) =
      adelicFiniteRealMixedFamily f v hv (b * a) :=
  (representation_hom_mul_apply (adelicCyclicHilbertRepresentation f) (adelicFiniteRealJointHom v hv)
    b a (adelicCyclicUnitReference f)).symm

variable (F : PrimitiveCuspForm N k)

/-- The genuine original selected finite/real tensor isometry intertwines its independent external action on every actual tensor vector. -/
theorem adelicFiniteRealTensorIsometry_intertwines (hv : Function.Injective v) (hk : 0 < k)
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ)
    (x : AdelicFiniteRealTensor F.toCuspForm v) :
    adelicFiniteRealTensorIsometry v F hv hk (adelicFiniteRealTensorRepresentation F.toCuspForm v b x) =
      adelicFiniteRealJointRepresentation F.toCuspForm v hv b (adelicFiniteRealTensorIsometry v F hv hk x) :=
  @linearMap_intertwines_of_spanning_family
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ)
    (AdelicFiniteRealTensor F.toCuspForm v) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteRealTensorRepresentation F.toCuspForm v) (adelicFiniteRealJointRepresentation F.toCuspForm v hv)
    (adelicFiniteRealTensorIsometry v F hv hk).toLinearMap
    (adelicFiniteRealTensorFamily F.toCuspForm v) (adelicFiniteRealMixedFamily F.toCuspForm v hv)
    (adelicFiniteRealTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))
    (adelicFiniteRealTensorIsometry_family v F hv hk)
    (adelicFiniteRealTensorFamily_action F.toCuspForm v) (adelicFiniteRealMixedFamily_action F.toCuspForm v hv) b x

end
end Dubon2026
