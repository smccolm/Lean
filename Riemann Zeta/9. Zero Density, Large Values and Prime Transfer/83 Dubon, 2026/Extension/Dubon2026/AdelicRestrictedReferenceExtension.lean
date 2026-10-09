import Dubon2026.AdelicRestrictedFiniteTensor
import Dubon2026.AdelicFiniteReferenceExtension
import Dubon2026.AdelicFiniteReferenceCoordinates
import Dubon2026.TensorReferenceInclusion

/-! # Original fixed-base finite tensors and genuine unit-reference transitions -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + 1) → HeightOneSpectrum ℤ)

/-- The genuine fixed-base transition inserts the original new local unit reference and retains the same base vector. -/
def adelicRestrictedReferenceExtension (hf : f ≠ 0) :
    AdelicRestrictedFiniteTensor f (fun i : Fin n => v i.castSucc) →ₗᵢ[ℂ] AdelicRestrictedFiniteTensor f v :=
  @TensorProduct.mapIsometry ℂ
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc)) (adelicRestrictedBaseCore f)
    (AdelicFiniteLocalTensor f v) (adelicRestrictedBaseCore f)
    inferInstance inferInstance inferInstance inferInstance (adelicRestrictedBaseCoreInner f)
    inferInstance inferInstance inferInstance (adelicRestrictedBaseCoreInner f)
    (adelicFiniteLocalReferenceExtension f hf v) LinearIsometry.id

/-- Every true fixed-base pure orbit tensor is extended by the actual identity local matrix. -/
theorem adelicRestrictedReferenceExtension_family (hf : f ≠ 0)
    (b : (∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) × adelicRestrictedBaseGroup N) :
    adelicRestrictedReferenceExtension f v hf
      (adelicRestrictedFiniteTensorFamily f (fun i : Fin n => v i.castSucc) b) =
      adelicRestrictedFiniteTensorFamily f v (Fin.snoc b.1 1, b.2) := by
  change TensorProduct.map (adelicFiniteLocalReferenceExtension f hf v).toLinearMap LinearMap.id
    (adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) b.1 ⊗ₜ[ℂ]
      adelicRestrictedBaseOrbit f b.2) = _
  rw [TensorProduct.map_tmul]
  exact congrArg (fun x => x ⊗ₜ[ℂ] adelicRestrictedBaseOrbit f b.2)
    (adelicFiniteLocalReferenceExtension_family f hf v b.1)

variable (F : PrimitiveCuspForm N k)

/-- The actual original adelic realization is unchanged by genuine fixed-base reference insertion. -/
theorem adelicRestrictedFiniteTensorIsometry_reference_extension (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicRestrictedFiniteTensor F.toCuspForm (fun i : Fin n => v i.castSucc)) :
    adelicRestrictedFiniteTensorIsometry v F hv hgood
      (adelicRestrictedReferenceExtension F.toCuspForm v (primitiveCuspForm_ne_zero F) x) =
      adelicRestrictedFiniteTensorIsometry (fun i : Fin n => v i.castSucc) F
        (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc) x := by
  have he : (adelicRestrictedFiniteTensorIsometry v F hv hgood).toLinearMap.comp
      (adelicRestrictedReferenceExtension F.toCuspForm v (primitiveCuspForm_ne_zero F)).toLinearMap =
      (adelicRestrictedFiniteTensorIsometry (fun i : Fin n => v i.castSucc) F
        (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc)).toLinearMap := by
    apply @linearMap_eq_of_spanning_family
      (AdelicRestrictedFiniteTensor F.toCuspForm (fun i : Fin n => v i.castSucc))
      (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
      ((∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) × adelicRestrictedBaseGroup N)
      (adelicRestrictedFiniteTensorFamily F.toCuspForm (fun i : Fin n => v i.castSucc))
      (adelicRestrictedFiniteTensorFamily_span F.toCuspForm (fun i : Fin n => v i.castSucc)
        (primitiveCuspForm_ne_zero F))
    intro b
    have h₁ := congrArg (adelicRestrictedFiniteTensorIsometry v F hv hgood)
      (adelicRestrictedReferenceExtension_family F.toCuspForm v (primitiveCuspForm_ne_zero F) b)
    have h₂ := adelicRestrictedFiniteTensorIsometry_family v F hv hgood (Fin.snoc b.1 1, b.2)
    have h₃ := adelicRestrictedFiniteTensorIsometry_family (fun i : Fin n => v i.castSucc) F
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc) b
    have hG := congrArg (fun c : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation F.toCuspForm (c * b.2.val) (adelicCyclicUnitReference F.toCuspForm))
      (adelicFinitePlaceProduct_snoc_one v hv b.1)
    exact h₁.trans (h₂.trans (hG.trans h₃.symm))
  exact DFunLike.congr_fun he x

end
end Dubon2026
