import Dubon2026.AdelicFiniteTensorCompletion
import Dubon2026.FiniteHilbertTensorAction
import Dubon2026.AdelicLocalAwayTensorAction

/-! # Genuine external finite tensor actions and exact original adelic equivariance -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin n → HeightOneSpectrum ℤ)

/-- The actual finite external tensor of the original local smooth algebraic representations. -/
def adelicFiniteLocalTensorRepresentation :
    Representation ℂ (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) (AdelicFiniteLocalTensor f v) :=
  @finiteHilbertTensorRepresentation n (fun i => adelicLocalInnerCarrier f (v i))
    (fun i => GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) (fun _ => inferInstance)
    (fun i => adelicLocalSmoothRepresentation f (v i))

/-- The original full remaining-coordinate action preserves its genuine algebraic unit-reference orbit span. -/
theorem adelicFiniteFamilyAwayCore_invariant (a : adelicFiniteFamilyAwayGroup v)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicFiniteFamilyAwayCore f v) :
    adelicFiniteFamilyAwayRepresentation f v a x ∈ adelicFiniteFamilyAwayCore f v :=
  @representationOrbitSpan_invariant (adelicFiniteFamilyAwayGroup v) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayRepresentation f v)
    (adelicCyclicUnitReference f) a x hx

/-- The genuine full complementary action restricted to its actual algebraic orbit core. -/
def adelicFiniteFamilyAwayCoreRepresentation :
    Representation ℂ (adelicFiniteFamilyAwayGroup v) (adelicFiniteFamilyAwayCore f v) :=
  Representation.subrepresentation (adelicFiniteFamilyAwayRepresentation f v) (adelicFiniteFamilyAwayCore f v)
    (fun a x hx => adelicFiniteFamilyAwayCore_invariant f v a x hx)

/-- The actual external tensor action of all original selected local factors and the genuine full complement. -/
def adelicFiniteFullTensorRepresentation :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
      (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  Representation.tprod ((adelicFiniteLocalTensorRepresentation f v).comp (MonoidHom.fst _ _))
    ((adelicFiniteFamilyAwayCoreRepresentation f v).comp (MonoidHom.snd _ _))

/-- The original full adelic representation in its actual finite local/full-complement coordinates. -/
def adelicFiniteFullJointRepresentation (hv : Function.Injective v) :
    Representation ℂ ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
      (AdelicCyclicHilbert f) :=
  (adelicCyclicHilbertRepresentation f).comp (adelicFiniteFamilyEquiv v hv).toMonoidHom

/-- The actual finite local tensor action multiplies every original local orbit coordinate. -/
theorem adelicFiniteLocalTensorFamily_action
    (b a : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) :
    adelicFiniteLocalTensorRepresentation f v b (adelicFiniteLocalTensorFamily f v a) =
      adelicFiniteLocalTensorFamily f v (b * a) :=
  @finiteHilbertTensorRepresentation_orbit_action n (fun i => adelicLocalInnerCarrier f (v i))
    (fun i => GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) (fun _ => inferInstance)
    (fun i => adelicLocalSmoothRepresentation f (v i)) (fun i => adelicLocalUnitReference f (v i)) a b

/-- The genuine full-complement core action has precisely its original orbit multiplication. -/
theorem adelicFiniteFamilyAwayOrbit_action (b a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFamilyAwayCoreRepresentation f v b (adelicFiniteFamilyAwayOrbit f v a) =
      adelicFiniteFamilyAwayOrbit f v (b * a) := by
  apply Subtype.ext
  exact (congrArg (fun T : Module.End ℂ (AdelicCyclicHilbert f) => T (adelicCyclicUnitReference f))
    (map_mul (adelicFiniteFamilyAwayRepresentation f v) b a)).symm

/-- The genuine finite local/full-complement tensor family transforms by exactly the original product group multiplication. -/
theorem adelicFiniteFullTensorFamily_action
    (b a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullTensorRepresentation f v b (adelicFiniteFullTensorFamily f v a) =
      adelicFiniteFullTensorFamily f v (b * a) := by
  change TensorProduct.map (adelicFiniteLocalTensorRepresentation f v b.1)
    (adelicFiniteFamilyAwayCoreRepresentation f v b.2)
    (adelicFiniteLocalTensorFamily f v a.1 ⊗ₜ[ℂ] adelicFiniteFamilyAwayOrbit f v a.2) = _
  rw [TensorProduct.map_tmul, adelicFiniteLocalTensorFamily_action, adelicFiniteFamilyAwayOrbit_action]
  rfl

/-- The original full mixed family has exactly the actual joint adelic orbit multiplication. -/
theorem adelicFiniteFullMixedFamily_action (hv : Function.Injective v)
    (b a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullJointRepresentation f v hv b (adelicFiniteFullMixedFamily f v hv a) =
      adelicFiniteFullMixedFamily f v hv (b * a) :=
  (congrArg (fun T : Module.End ℂ (AdelicCyclicHilbert f) => T (adelicCyclicUnitReference f))
    (map_mul (adelicFiniteFullJointRepresentation f v hv) b a)).symm

variable (F : PrimitiveCuspForm N k) (hv : Function.Injective v)

/-- The actual finite-family Hilbert tensor isometry intertwines the genuine external tensor action and the original full adelic action. -/
theorem adelicFiniteFullTensorIsometry_intertwines (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (x : AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteFullTensorRepresentation F.toCuspForm v b x) =
      adelicFiniteFullJointRepresentation F.toCuspForm v hv b (adelicFiniteFullTensorIsometry F v hv hgood x) :=
  @linearMap_intertwines_of_spanning_family
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorRepresentation F.toCuspForm v) (adelicFiniteFullJointRepresentation F.toCuspForm v hv)
    (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap
    (adelicFiniteFullTensorFamily F.toCuspForm v) (adelicFiniteFullMixedFamily F.toCuspForm v hv)
    (adelicFiniteFullTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))
    (adelicFiniteFullTensorIsometry_family F v hv hgood)
    (adelicFiniteFullTensorFamily_action F.toCuspForm v) (adelicFiniteFullMixedFamily_action F.toCuspForm v hv) b x

end
end Dubon2026
