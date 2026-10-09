import Dubon2026.AdelicGoodTail
import Dubon2026.AdelicRestrictedFiniteTensorAction

/-! # Actual level tails fix genuine finite tensor images -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)

omit [NeZero N] in
/-- The actual good tail commutes with every genuine finite-local and fixed-base product. -/
theorem adelicGoodTail_joint_commute (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (a : RationalAdelicGL2)
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    Commute (adelicGoodTail N v hv a) (adelicFinitePlaceProduct v hv b.1 * b.2.val) := by
  let r : adelicFiniteFamilyAwayGroup v := ⟨adelicGoodTail N v hv a, funext (adelicGoodTail_same N v hv a)⟩
  have hlocal : Commute (adelicGoodTail N v hv a) (adelicFinitePlaceProduct v hv b.1) :=
    (adelicFinitePlaceProduct_away_commute v hv b.1 r).symm
  exact hlocal.mul_right (adelicGoodTail_base_commute N v hv hgood a b.2)

variable (F : PrimitiveCuspForm N k)

/-- Every actual finite tensor image is fixed by an original good tail whose remaining coordinates are in genuine local level. -/
theorem adelicGoodTail_fixes_finite_image (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i, w ≠ v i) → adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w)
    (x : AdelicRestrictedFiniteTensor F.toCuspForm v) :
    adelicCyclicHilbertRepresentation F.toCuspForm (adelicGoodTail N v hv a)
      (adelicRestrictedFiniteTensorIsometry v F hv hgood x) = adelicRestrictedFiniteTensorIsometry v F hv hgood x := by
  have he : (adelicCyclicHilbertRepresentation F.toCuspForm (adelicGoodTail N v hv a)).comp
      (adelicRestrictedFiniteTensorIsometry v F hv hgood).toLinearMap =
      (adelicRestrictedFiniteTensorIsometry v F hv hgood).toLinearMap := by
    apply @linearMap_eq_of_spanning_family (AdelicRestrictedFiniteTensor F.toCuspForm v)
      (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
      ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
      (adelicRestrictedFiniteTensorFamily F.toCuspForm v)
      (adelicRestrictedFiniteTensorFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))
    intro b
    have himage := adelicRestrictedFiniteTensorIsometry_family v F hv hgood b
    have hc := (adelicGoodTail_joint_commute v hv hgood a b).map (adelicCyclicHilbertRepresentation F.toCuspForm)
    have hcomm := congrArg (fun T : Module.End ℂ (AdelicCyclicHilbert F.toCuspForm) =>
      T (adelicCyclicUnitReference F.toCuspForm)) hc.eq
    have hfix := adelicGoodTail_unitReference N v hv F.toCuspForm hgood a ha
    have hmid := hcomm.trans (congrArg
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFinitePlaceProduct v hv b.1 * b.2.val)) hfix)
    exact (congrArg (adelicCyclicHilbertRepresentation F.toCuspForm (adelicGoodTail N v hv a)) himage).trans
      (hmid.trans himage.symm)
  exact DFunLike.congr_fun he x

/-- At every sufficiently large genuine finite tensor stage, the independent external action agrees exactly with the full original adelic action. -/
theorem adelicRestrictedFiniteTensor_full_intertwines (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i, w ≠ v i) → adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w)
    (x : AdelicRestrictedFiniteTensor F.toCuspForm v) :
    adelicRestrictedFiniteTensorIsometry v F hv hgood
      (adelicRestrictedFiniteTensorRepresentation F.toCuspForm v
        (adelicFinitePlaceEvaluation v a, adelicBaseProjection N a) x) =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicRestrictedFiniteTensorIsometry v F hv hgood x) := by
  let b := (adelicFinitePlaceEvaluation v a, adelicBaseProjection N a)
  have hstage := adelicRestrictedFiniteTensorIsometry_intertwines v F hv hgood b x
  have htail := adelicGoodTail_fixes_finite_image v hv F hgood a ha x
  have hmul := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation F.toCuspForm) (MonoidHom.id _)
    (adelicFinitePlaceProduct v hv b.1 * b.2.val) (adelicGoodTail N v hv a)
    (adelicRestrictedFiniteTensorIsometry v F hv hgood x)
  have hmulfix := hmul.trans (congrArg
    (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFinitePlaceProduct v hv b.1 * b.2.val)) htail)
  have hactual := congrArg (fun c : RationalAdelicGL2 =>
    adelicCyclicHilbertRepresentation F.toCuspForm c (adelicRestrictedFiniteTensorIsometry v F hv hgood x))
    (adelicFiniteProduct_base_tail N v hv hgood a)
  exact hstage.trans (hmulfix.symm.trans hactual)

end
end Dubon2026
