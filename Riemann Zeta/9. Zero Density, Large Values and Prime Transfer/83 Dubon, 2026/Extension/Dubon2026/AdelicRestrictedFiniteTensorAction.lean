import Dubon2026.AdelicRestrictedFiniteTensor
import Dubon2026.AdelicFiniteTensorAction

/-! # Genuine external actions on finite good-place tensors with the fixed original base -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)

/-- The actual fixed-base action preserves its genuine original unit-reference orbit core. -/
theorem adelicRestrictedBaseCore_invariant (a : adelicRestrictedBaseGroup N)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicRestrictedBaseCore f) :
    adelicRestrictedBaseRepresentation f a x ∈ adelicRestrictedBaseCore f :=
  @representationOrbitSpan_invariant (adelicRestrictedBaseGroup N) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicRestrictedBaseRepresentation f)
    (adelicCyclicUnitReference f) a x hx

/-- The genuine fixed-base representation on its actual original algebraic orbit core. -/
def adelicRestrictedBaseCoreRepresentation :
    Representation ℂ (adelicRestrictedBaseGroup N) (adelicRestrictedBaseCore f) :=
  Representation.subrepresentation (adelicRestrictedBaseRepresentation f) (adelicRestrictedBaseCore f)
    (fun a x hx => adelicRestrictedBaseCore_invariant f a x hx)

/-- The original fixed-base core action multiplies the literal original orbit coordinate. -/
theorem adelicRestrictedBaseOrbit_action (b a : adelicRestrictedBaseGroup N) :
    adelicRestrictedBaseCoreRepresentation f b (adelicRestrictedBaseOrbit f a) =
      adelicRestrictedBaseOrbit f (b * a) := by
  apply Subtype.ext
  exact (congrArg (fun T : Module.End ℂ (AdelicCyclicHilbert f) => T (adelicCyclicUnitReference f))
    (map_mul (adelicRestrictedBaseRepresentation f) b a)).symm

/-- The genuine external tensor action uses the original local representations and the original fixed-base core action. -/
def adelicRestrictedFiniteTensorRepresentation :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
      (AdelicRestrictedFiniteTensor f v) :=
  Representation.tprod ((adelicFiniteLocalTensorRepresentation f v).comp (MonoidHom.fst _ _))
    ((adelicRestrictedBaseCoreRepresentation f).comp (MonoidHom.snd _ _))

/-- Actual external finite tensor actions multiply the original selected local and fixed-base orbit coordinates. -/
theorem adelicRestrictedFiniteTensorFamily_action
    (b a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedFiniteTensorRepresentation f v b (adelicRestrictedFiniteTensorFamily f v a) =
      adelicRestrictedFiniteTensorFamily f v (b * a) := by
  change TensorProduct.map (adelicFiniteLocalTensorRepresentation f v b.1)
    (adelicRestrictedBaseCoreRepresentation f b.2)
    (adelicFiniteLocalTensorFamily f v a.1 ⊗ₜ[ℂ] adelicRestrictedBaseOrbit f a.2) = _
  rw [TensorProduct.map_tmul, adelicFiniteLocalTensorFamily_action, adelicRestrictedBaseOrbit_action]
  rfl

/-- Multiplication of the true finite local factors and the true fixed base is a genuine original group homomorphism. -/
def adelicRestrictedFiniteJointHom (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) →* RationalAdelicGL2 :=
  (adelicFiniteFamilyEquiv v hv).toMonoidHom.comp
    ((MonoidHom.id _).prodMap (adelicRestrictedBaseToFiniteAway v hgood))

omit [NeZero N] in
/-- The actual fixed-base joint homomorphism is exactly the original finite local product times the original base matrix. -/
theorem adelicRestrictedFiniteJointHom_apply (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedFiniteJointHom v hv hgood b = adelicFinitePlaceProduct v hv b.1 * b.2.val := rfl

/-- The original adelic representation in the actual finite-local and fixed-base coordinates. -/
def adelicRestrictedFiniteJointRepresentation (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
      (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp (adelicRestrictedFiniteJointHom v hv hgood)

/-- The literal original mixed orbit family under the true selected local and fixed-base groups. -/
def adelicRestrictedFiniteMixedFamily (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    AdelicCyclicHilbert f :=
  adelicRestrictedFiniteJointRepresentation f v hv hgood b (adelicCyclicUnitReference f)

/-- The actual original mixed orbit family transforms by the genuine product-group multiplication. -/
theorem adelicRestrictedFiniteMixedFamily_action (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedFiniteJointRepresentation f v hv hgood b (adelicRestrictedFiniteMixedFamily f v hv hgood a) =
      adelicRestrictedFiniteMixedFamily f v hv hgood (b * a) :=
  (congrArg (fun T : Module.End ℂ (AdelicCyclicHilbert f) => T (adelicCyclicUnitReference f))
    (map_mul (adelicRestrictedFiniteJointRepresentation f v hv hgood) b a)).symm

variable (F : PrimitiveCuspForm N k)

/-- The original finite tensor isometry intertwines the independently constructed actual external action on every tensor vector. -/
theorem adelicRestrictedFiniteTensorIsometry_intertwines (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
    (x : AdelicRestrictedFiniteTensor F.toCuspForm v) :
    adelicRestrictedFiniteTensorIsometry v F hv hgood (adelicRestrictedFiniteTensorRepresentation F.toCuspForm v b x) =
      adelicRestrictedFiniteJointRepresentation F.toCuspForm v hv hgood b
        (adelicRestrictedFiniteTensorIsometry v F hv hgood x) :=
  @linearMap_intertwines_of_spanning_family
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
    (AdelicRestrictedFiniteTensor F.toCuspForm v) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicRestrictedFiniteTensorRepresentation F.toCuspForm v)
    (adelicRestrictedFiniteJointRepresentation F.toCuspForm v hv hgood)
    (adelicRestrictedFiniteTensorIsometry v F hv hgood).toLinearMap
    (adelicRestrictedFiniteTensorFamily F.toCuspForm v) (adelicRestrictedFiniteMixedFamily F.toCuspForm v hv hgood)
    (adelicRestrictedFiniteTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))
    (adelicRestrictedFiniteTensorIsometry_family v F hv hgood)
    (adelicRestrictedFiniteTensorFamily_action F.toCuspForm v)
    (adelicRestrictedFiniteMixedFamily_action F.toCuspForm v hv hgood) b x

end
end Dubon2026
