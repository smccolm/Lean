import Dubon2026.AdelicFiniteTensorAssociation
import Dubon2026.TensorReferenceInclusion
import Dubon2026.LinearIsometryCompletionFunctor
import Dubon2026.AdelicFiniteTensorCompletion

/-! # Genuine blocked orbit realizations agree with the original finite tensor realization -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n m : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + m) → HeightOneSpectrum ℤ)

/-- The actual original coordinates of two adjacent finite blocks and their full remaining complement. -/
abbrev AdelicFiniteBlockedCoordinates :=
  ((∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ)) ×
    (∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ))) × adelicFiniteFamilyAwayGroup v

/-- The genuine blocked pure orbit family is indexed by its actual original group coordinates. -/
def adelicFiniteBlockedOrbitFamily (b : AdelicFiniteBlockedCoordinates v) : AdelicFiniteBlockedTensor f v :=
  adelicFiniteBlockedFamily f v b.1.1 b.1.2 b.2

/-- The original blocked orbit family spans the entire genuine blocked tensor. -/
theorem adelicFiniteBlockedOrbitFamily_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteBlockedOrbitFamily f v)) = ⊤ := by
  apply @tensorFamily_span_eq_top
    ((∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ)) ×
      (∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ)))
    (adelicFiniteFamilyAwayGroup v) (adelicFiniteBlockPairCarrier f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance
    (fun b => adelicFiniteLocalTensorFamily f (fun i : Fin n => v (Fin.castAdd m i)) b.1 ⊗ₜ[ℂ]
      adelicFiniteLocalTensorFamily f (fun j : Fin m => v (Fin.natAdd n j)) b.2)
    (adelicFiniteFamilyAwayOrbit f v) _ (adelicFiniteFamilyAwayOrbit_span f v)
  exact tensorFamily_span_eq_top
    (adelicFiniteLocalTensorFamily f (fun i : Fin n => v (Fin.castAdd m i)))
    (adelicFiniteLocalTensorFamily f (fun j : Fin m => v (Fin.natAdd n j)))
    (adelicFiniteLocalTensorFamily_span f (fun i : Fin n => v (Fin.castAdd m i)) hf)
    (adelicFiniteLocalTensorFamily_span f (fun j : Fin m => v (Fin.natAdd n j)) hf)

/-- The literal original cusp orbit under multiplication of the two actual blocks and the actual complement. -/
def adelicFiniteBlockedOrbitImage (hv : Function.Injective v) (b : AdelicFiniteBlockedCoordinates v) :
    AdelicCyclicHilbert f :=
  adelicCyclicHilbertRepresentation f
    (adelicFinitePlaceProduct (fun i : Fin n => v (Fin.castAdd m i)) (adelicPlaceFamily_left_injective v hv) b.1.1 *
      adelicFinitePlaceProduct (fun j : Fin m => v (Fin.natAdd n j)) (adelicPlaceFamily_right_injective v hv) b.1.2 * b.2.val)
    (adelicCyclicUnitReference f)

variable (F : PrimitiveCuspForm N k)

/-- The genuine blocked orbit tensors have exactly the Gram matrix of their literal original adelic orbit vectors. -/
theorem adelicFiniteBlockedOrbitFamily_gram (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (a b : AdelicFiniteBlockedCoordinates v) :
    inner ℂ (adelicFiniteBlockedOrbitFamily F.toCuspForm v a) (adelicFiniteBlockedOrbitFamily F.toCuspForm v b) =
      inner ℂ (adelicFiniteBlockedOrbitImage F.toCuspForm v hv a) (adelicFiniteBlockedOrbitImage F.toCuspForm v hv b) := by
  let T : AdelicFiniteBlockedTensor F.toCuspForm v →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
    (adelicFiniteFullTensorIsometry F v hv hgood).comp (adelicFiniteTensorAssociation F.toCuspForm v)
  have ha : T (adelicFiniteBlockedOrbitFamily F.toCuspForm v a) = adelicFiniteBlockedOrbitImage F.toCuspForm v hv a :=
    adelicFiniteTensorAssociation_original_orbit v F hv hgood a.1.1 a.1.2 a.2
  have hb : T (adelicFiniteBlockedOrbitFamily F.toCuspForm v b) = adelicFiniteBlockedOrbitImage F.toCuspForm v hv b :=
    adelicFiniteTensorAssociation_original_orbit v F hv hgood b.1.1 b.1.2 b.2
  have hi : inner ℂ (T (adelicFiniteBlockedOrbitFamily F.toCuspForm v a))
      (T (adelicFiniteBlockedOrbitFamily F.toCuspForm v b)) =
      inner ℂ (adelicFiniteBlockedOrbitFamily F.toCuspForm v a)
        (adelicFiniteBlockedOrbitFamily F.toCuspForm v b) :=
    @LinearIsometry.inner_map_map ℂ (AdelicFiniteBlockedTensor F.toCuspForm v)
      inferInstance inferInstance inferInstance (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance T _ _
  exact hi.symm.trans (congrArg₂ (inner ℂ) ha hb)

/-- The canonical Gram realization of the genuine blocked tensor uses its literal original adelic orbit vectors. -/
def adelicFiniteBlockedTensorIsometry (hv : Function.Injective v) (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    AdelicFiniteBlockedTensor F.toCuspForm v →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  gramSpanningIsometry (adelicFiniteBlockedOrbitFamily F.toCuspForm v) (adelicFiniteBlockedOrbitImage F.toCuspForm v hv)
    (adelicFiniteBlockedOrbitFamily_gram v F hv hgood)
    (adelicFiniteBlockedOrbitFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))

/-- The genuine blocked realization recovers every literal original adelic orbit vector. -/
theorem adelicFiniteBlockedTensorIsometry_family (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (a : AdelicFiniteBlockedCoordinates v) :
    adelicFiniteBlockedTensorIsometry v F hv hgood (adelicFiniteBlockedOrbitFamily F.toCuspForm v a) =
      adelicFiniteBlockedOrbitImage F.toCuspForm v hv a :=
  gramSpanningIsometry_family _ _ _ _ a

/-- For every genuine algebraic blocked tensor, grouping adjacent local factors preserves its original adelic realization. -/
theorem adelicFiniteTensorIsometry_association (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : AdelicFiniteBlockedTensor F.toCuspForm v) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteTensorAssociation F.toCuspForm v x) =
      adelicFiniteBlockedTensorIsometry v F hv hgood x := by
  have he : (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap.comp
      (adelicFiniteTensorAssociation F.toCuspForm v).toLinearMap =
      (adelicFiniteBlockedTensorIsometry v F hv hgood).toLinearMap := by
    apply @linearMap_eq_of_spanning_family (AdelicFiniteBlockedTensor F.toCuspForm v)
      (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
      (AdelicFiniteBlockedCoordinates v) (adelicFiniteBlockedOrbitFamily F.toCuspForm v)
      (adelicFiniteBlockedOrbitFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))
    intro a
    exact (adelicFiniteTensorAssociation_original_orbit v F hv hgood a.1.1 a.1.2 a.2).trans
      (adelicFiniteBlockedTensorIsometry_family v F hv hgood a).symm
  exact DFunLike.congr_fun he x

/-- The completed grouping of adjacent genuine blocks retains exactly the original completed adelic realization. -/
theorem adelicFiniteHilbertTensorIsometry_association (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : Completion (AdelicFiniteBlockedTensor F.toCuspForm v)) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood
      (linearIsometryCompletionFunctor (adelicFiniteTensorAssociation F.toCuspForm v) x) =
      @linearIsometryCompletion (AdelicFiniteBlockedTensor F.toCuspForm v)
        (AdelicCyclicHilbert F.toCuspForm)
        inferInstance inferInstance inferInstance inferInstance inferInstance
        (adelicFiniteBlockedTensorIsometry v F hv hgood) x :=
  @linearIsometryCompletion_diagram (AdelicFiniteBlockedTensor F.toCuspForm v)
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteTensorAssociation F.toCuspForm v) (adelicFiniteFullTensorIsometry F v hv hgood)
    (adelicFiniteBlockedTensorIsometry v F hv hgood) (adelicFiniteTensorIsometry_association v F hv hgood) x

end
end Dubon2026
