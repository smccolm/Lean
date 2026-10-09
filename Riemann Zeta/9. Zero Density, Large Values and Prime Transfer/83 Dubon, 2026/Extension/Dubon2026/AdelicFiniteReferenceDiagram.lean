import Dubon2026.AdelicFiniteReferenceCore
import Dubon2026.AdelicFiniteReferenceExtension
import Dubon2026.AdelicFiniteTensorIsometry
import Dubon2026.TensorReferenceInclusion

/-! # Original adelic realization commutes with actual finite tensor reference insertion -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + 1) → HeightOneSpectrum ℤ)

/-- The genuine common tensor domain uses the original shorter local family and the actual smaller complement. -/
abbrev AdelicFiniteReferenceDomain :=
  AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc) ⊗[ℂ] adelicFiniteFamilyAwayCore f v

/-- The common reference domain has its genuine inherited binary Hilbert tensor norm. -/
instance adelicFiniteReferenceDomainNormed : NormedAddCommGroup (AdelicFiniteReferenceDomain f v) :=
  @TensorProduct.instNormedAddCommGroup ℂ
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc)) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)

/-- The common reference domain has the original product inner product. -/
instance adelicFiniteReferenceDomainInner : InnerProductSpace ℂ (AdelicFiniteReferenceDomain f v) :=
  @TensorProduct.instInnerProductSpace ℂ
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc)) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)

/-- The genuine common-domain orbit tensors retain both original factor vectors. -/
def adelicFiniteReferenceFamily
    (b : (∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    AdelicFiniteReferenceDomain f v :=
  adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) b.1 ⊗ₜ[ℂ] adelicFiniteFamilyAwayOrbit f v b.2

/-- The actual common-domain orbit tensors span the entire genuine tensor domain. -/
theorem adelicFiniteReferenceFamily_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (adelicFiniteReferenceFamily f v)) = ⊤ :=
  @tensorFamily_span_eq_top
    (∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) (adelicFiniteFamilyAwayGroup v)
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc)) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc)) (adelicFiniteFamilyAwayOrbit f v)
    (adelicFiniteLocalTensorFamily_span f (fun i : Fin n => v i.castSucc) hf) (adelicFiniteFamilyAwayOrbit_span f v)

/-- The shorter route retains local tensors and includes their identical original complementary vectors. -/
def adelicFiniteReferenceToShorter : AdelicFiniteReferenceDomain f v →ₗᵢ[ℂ]
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc) ⊗[ℂ]
      adelicFiniteFamilyAwayCore f (fun i : Fin n => v i.castSucc)) :=
  @TensorProduct.mapIsometry ℂ
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc)) (adelicFiniteFamilyAwayCore f v)
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc))
      (adelicFiniteFamilyAwayCore f (fun i : Fin n => v i.castSucc))
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f (fun i : Fin n => v i.castSucc))
    LinearIsometry.id (adelicFiniteFamilyAwayCoreInitIsometry f v)

/-- The longer route appends the genuine original local unit reference and keeps the actual complement fixed. -/
def adelicFiniteReferenceToLonger (hf : f ≠ 0) : AdelicFiniteReferenceDomain f v →ₗᵢ[ℂ]
    (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  @TensorProduct.mapIsometry ℂ
    (AdelicFiniteLocalTensor f (fun i : Fin n => v i.castSucc)) (adelicFiniteFamilyAwayCore f v)
    (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    (adelicFiniteLocalReferenceExtension f hf v) LinearIsometry.id

/-- The shorter tensor inclusion preserves the literal original pure orbit family. -/
theorem adelicFiniteReferenceToShorter_family
    (b : (∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteReferenceToShorter f v (adelicFiniteReferenceFamily f v b) =
      adelicFiniteFullTensorFamily f (fun i : Fin n => v i.castSucc) (b.1, adelicFiniteFamilyAwayInitHom v b.2) := by
  change TensorProduct.map (LinearMap.id)
    (adelicFiniteFamilyAwayCoreInitIsometry f v).toLinearMap
    (adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) b.1 ⊗ₜ[ℂ]
      adelicFiniteFamilyAwayOrbit f v b.2) = _
  rw [TensorProduct.map_tmul]
  exact congrArg (fun y => adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) b.1 ⊗ₜ[ℂ] y)
    (adelicFiniteFamilyAwayCoreInitIsometry_orbit f v b.2)

/-- The longer tensor inclusion inserts exactly the actual identity-place orbit factor. -/
theorem adelicFiniteReferenceToLonger_family (hf : f ≠ 0)
    (b : (∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteReferenceToLonger f v hf (adelicFiniteReferenceFamily f v b) =
      adelicFiniteFullTensorFamily f v (Fin.snoc b.1 1, b.2) := by
  change TensorProduct.map (adelicFiniteLocalReferenceExtension f hf v).toLinearMap LinearMap.id
    (adelicFiniteLocalTensorFamily f (fun i : Fin n => v i.castSucc) b.1 ⊗ₜ[ℂ]
      adelicFiniteFamilyAwayOrbit f v b.2) = _
  rw [TensorProduct.map_tmul]
  exact congrArg (fun x => x ⊗ₜ[ℂ] adelicFiniteFamilyAwayOrbit f v b.2)
    (adelicFiniteLocalReferenceExtension_family f hf v b.1)

variable (F : PrimitiveCuspForm N k)

/-- Adding the actual new local unit reference preserves the original adelic realization of every common-domain tensor vector. -/
theorem adelicFiniteTensorIsometry_reference_extension (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : AdelicFiniteReferenceDomain F.toCuspForm v) :
    adelicFiniteFullTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc)
      (adelicFiniteReferenceToShorter F.toCuspForm v x) =
      adelicFiniteFullTensorIsometry F v hv hgood
        (adelicFiniteReferenceToLonger F.toCuspForm v (primitiveCuspForm_ne_zero F) x) := by
  have he : (adelicFiniteFullTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc)).toLinearMap.comp
      (adelicFiniteReferenceToShorter F.toCuspForm v).toLinearMap =
      (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap.comp
        (adelicFiniteReferenceToLonger F.toCuspForm v (primitiveCuspForm_ne_zero F)).toLinearMap := by
    apply @linearMap_eq_of_spanning_family (AdelicFiniteReferenceDomain F.toCuspForm v)
      (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance
      ((∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v i.castSucc).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
      (adelicFiniteReferenceFamily F.toCuspForm v)
      (adelicFiniteReferenceFamily_span F.toCuspForm v (primitiveCuspForm_ne_zero F))
    intro b
    have h₁ := congrArg (adelicFiniteFullTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc))
      (adelicFiniteReferenceToShorter_family F.toCuspForm v b)
    have h₂ := adelicFiniteFullTensorIsometry_family F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc) (b.1, adelicFiniteFamilyAwayInitHom v b.2)
    have h₃ := congrArg (adelicFiniteFullTensorIsometry F v hv hgood)
      (adelicFiniteReferenceToLonger_family F.toCuspForm v (primitiveCuspForm_ne_zero F) b)
    have h₄ := adelicFiniteFullTensorIsometry_family F v hv hgood (Fin.snoc b.1 1, b.2)
    have hG : adelicFiniteFamilyEquiv v hv (Fin.snoc b.1 1, b.2) =
        adelicFiniteFamilyEquiv (fun i : Fin n => v i.castSucc) (hv.comp (Fin.castSucc_injective n))
          (b.1, adelicFiniteFamilyAwayInitHom v b.2) :=
      congrArg (fun c : RationalAdelicGL2 => c * b.2.val) (adelicFinitePlaceProduct_snoc_one v hv b.1)
    have h₅ := congrArg (fun c => adelicCyclicHilbertRepresentation F.toCuspForm c
      (adelicCyclicUnitReference F.toCuspForm)) hG
    exact h₁.trans (h₂.trans (h₅.symm.trans (h₄.symm.trans h₃.symm)))
  exact DFunLike.congr_fun he x

end
end Dubon2026
