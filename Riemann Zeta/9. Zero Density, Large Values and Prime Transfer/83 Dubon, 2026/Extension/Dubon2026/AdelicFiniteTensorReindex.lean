import Dubon2026.AdelicFiniteFamilyReindex
import Dubon2026.FiniteHilbertTensorReindex
import Dubon2026.AdelicFiniteTensorIsometry
import Dubon2026.TensorReferenceInclusion

/-! # Genuine finite tensor permutations preserve the original adelic realization -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
  (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n))

/-- Permuting the actual finite places preserves exactly the original complementary orbit submodule. -/
theorem adelicFiniteFamilyAwayCore_reindex :
    adelicFiniteFamilyAwayCore f (fun i => v (e i)) = adelicFiniteFamilyAwayCore f v := by
  exact congrArg (fun H : Subgroup RationalAdelicGL2 =>
    Submodule.span ℂ (Set.range (fun a : H =>
      adelicCyclicHilbertRepresentation f a.val (adelicCyclicUnitReference f))))
    (adelicFiniteFamilyAwayGroup_reindex v e)

/-- The reordered complementary core is identified by the identity on original Hilbert vectors. -/
def adelicFiniteFamilyAwayCoreReindex :
    adelicFiniteFamilyAwayCore f (fun i => v (e i)) ≃ₗᵢ[ℂ] adelicFiniteFamilyAwayCore f v :=
  LinearIsometryEquiv.ofEq _ _ (adelicFiniteFamilyAwayCore_reindex f v e)

/-- Reordering genuine local tensors and retaining the identical complementary vectors is an actual tensor isometry. -/
def adelicFiniteFullTensorReindex :
    (AdelicFiniteLocalTensor f (fun i => v (e i)) ⊗[ℂ] adelicFiniteFamilyAwayCore f (fun i => v (e i))) →ₗᵢ[ℂ]
      (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  @TensorProduct.mapIsometry ℂ
    (AdelicFiniteLocalTensor f (fun i => v (e i))) (adelicFiniteFamilyAwayCore f (fun i => v (e i)))
    (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f (fun i => v (e i)))
    inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    (finiteHilbertTensorReindexIsometry (fun i => adelicLocalInnerCarrier f (v i)) e)
    (adelicFiniteFamilyAwayCoreReindex f v e).toLinearIsometry

/-- Genuine tensor permutation sends original pure orbit vectors to the same factors in their original order. -/
theorem adelicFiniteFullTensorReindex_family
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup (fun i => v (e i))) :
    adelicFiniteFullTensorReindex f v e
      (adelicFiniteFullTensorFamily f (fun i => v (e i)) ((fun i => g (e i)), a)) =
      adelicFiniteFullTensorFamily f v (g, adelicFiniteFamilyAwayReindex v e a) := by
  change TensorProduct.map
    (finiteHilbertTensorReindexIsometry (fun i => adelicLocalInnerCarrier f (v i)) e).toLinearMap
    (adelicFiniteFamilyAwayCoreReindex f v e).toLinearEquiv.toLinearMap
    (adelicFiniteLocalTensorFamily f (fun i => v (e i)) (fun i => g (e i)) ⊗ₜ[ℂ]
      adelicFiniteFamilyAwayOrbit f (fun i => v (e i)) a) = _
  rw [TensorProduct.map_tmul]
  have hlocal := finiteHilbertTensorReindexIsometry_pure (fun i => adelicLocalInnerCarrier f (v i)) e
    (fun i => adelicLocalUnitOrbit f (v i) (g i))
  have haway : adelicFiniteFamilyAwayCoreReindex f v e
      (adelicFiniteFamilyAwayOrbit f (fun i => v (e i)) a) =
      adelicFiniteFamilyAwayOrbit f v (adelicFiniteFamilyAwayReindex v e a) := by
    apply Subtype.ext
    exact (LinearIsometryEquiv.coe_ofEq_apply (adelicFiniteFamilyAwayCore_reindex f v e)
      (adelicFiniteFamilyAwayOrbit f (fun i => v (e i)) a)).trans
      (congrArg (fun c => adelicCyclicHilbertRepresentation f c (adelicCyclicUnitReference f))
        (MulEquiv.subgroupCongr_apply (adelicFiniteFamilyAwayGroup_reindex v e) a)).symm
  exact congrArg₂ (fun (x : AdelicFiniteLocalTensor f v) (y : adelicFiniteFamilyAwayCore f v) =>
    x ⊗ₜ[ℂ] y) hlocal haway

variable (F : PrimitiveCuspForm N k)

/-- For every original tensor vector, genuine finite reordering leaves its original adelic Hilbert realization exactly unchanged. -/
theorem adelicFiniteFullTensorIsometry_reindex (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteLocalTensor F.toCuspForm (fun i => v (e i)) ⊗[ℂ]
      adelicFiniteFamilyAwayCore F.toCuspForm (fun i => v (e i))) :
    adelicFiniteFullTensorIsometry F v hv hgood (adelicFiniteFullTensorReindex F.toCuspForm v e x) =
      adelicFiniteFullTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i)) x := by
  have he : (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap.comp
      (adelicFiniteFullTensorReindex F.toCuspForm v e).toLinearMap =
      (adelicFiniteFullTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i))).toLinearMap := by
    apply @linearMap_eq_of_spanning_family
      (AdelicFiniteLocalTensor F.toCuspForm (fun i => v (e i)) ⊗[ℂ]
        adelicFiniteFamilyAwayCore F.toCuspForm (fun i => v (e i)))
      (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance inferInstance inferInstance
      ((∀ i, GeneralLinearGroup (Fin 2) ((v (e i)).adicCompletion ℚ)) ×
        adelicFiniteFamilyAwayGroup (fun i => v (e i)))
      (adelicFiniteFullTensorFamily F.toCuspForm (fun i => v (e i)))
      (adelicFiniteFullTensorFamily_span F.toCuspForm (fun i => v (e i)) (primitiveCuspForm_ne_zero F))
    rintro ⟨b, a⟩
    apply forall_reindexed_tuple (fun i => GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) e
      (fun b => adelicFiniteFullTensorIsometry F v hv hgood
        (adelicFiniteFullTensorReindex F.toCuspForm v e
          (adelicFiniteFullTensorFamily F.toCuspForm (fun i => v (e i)) (b, a))) =
        adelicFiniteFullTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i))
          (adelicFiniteFullTensorFamily F.toCuspForm (fun i => v (e i)) (b, a))) _ b
    intro g
    change adelicFiniteFullTensorIsometry F v hv hgood
      (adelicFiniteFullTensorReindex F.toCuspForm v e
        (adelicFiniteFullTensorFamily F.toCuspForm (fun i => v (e i)) ((fun i => g (e i)), a))) = _
    have h₁ := congrArg (adelicFiniteFullTensorIsometry F v hv hgood)
      (adelicFiniteFullTensorReindex_family F.toCuspForm v e g a)
    have h₂ := adelicFiniteFullTensorIsometry_family F v hv hgood
      (g, adelicFiniteFamilyAwayReindex v e a)
    have h₃ := adelicFiniteFullTensorIsometry_family F (fun i => v (e i))
      (hv.comp e.injective) (fun i => hgood (e i)) ((fun i => g (e i)), a)
    have h₄ := congrArg (fun c => adelicCyclicHilbertRepresentation F.toCuspForm c
      (adelicCyclicUnitReference F.toCuspForm)) (adelicFiniteFamilyEquiv_reindex v e hv g a).symm
    exact h₁.trans (h₂.trans (h₄.trans h₃.symm))
  exact DFunLike.congr_fun he x

end
end Dubon2026
