import Dubon2026.FiniteHilbertTensorAssociation
import Dubon2026.AdelicFiniteAssociationCoordinates
import Dubon2026.AdelicFiniteTensorIsometry

/-! # Genuine grouping of original local tensor blocks and exact original adelic orbit images -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n m : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + m) → HeightOneSpectrum ℤ)

/-- The actual binary Hilbert tensor of two adjacent original finite local blocks. -/
def adelicFiniteBlockPairCarrier : ComplexInnerCarrier :=
  ComplexInnerCarrier.tensor
    (finiteHilbertTensor n (fun i => adelicLocalInnerCarrier f (v (Fin.castAdd m i))))
    (finiteHilbertTensor m (fun j => adelicLocalInnerCarrier f (v (Fin.natAdd n j))))

/-- The genuine blocked tensor retains the same original full complementary orbit core. -/
abbrev AdelicFiniteBlockedTensor := adelicFiniteBlockPairCarrier f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v

/-- The genuine blocked tensor has the true product Hilbert norm. -/
instance adelicFiniteBlockedTensorNormed : NormedAddCommGroup (AdelicFiniteBlockedTensor f v) :=
  @TensorProduct.instNormedAddCommGroup ℂ (adelicFiniteBlockPairCarrier f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)

/-- The genuine blocked tensor has the true original product inner product. -/
instance adelicFiniteBlockedTensorInner : InnerProductSpace ℂ (AdelicFiniteBlockedTensor f v) :=
  @TensorProduct.instInnerProductSpace ℂ (adelicFiniteBlockPairCarrier f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)

/-- The actual grouping map joins the genuine finite local blocks and retains every original complementary vector. -/
def adelicFiniteTensorAssociation : AdelicFiniteBlockedTensor f v →ₗᵢ[ℂ]
    (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v) :=
  @TensorProduct.mapIsometry ℂ (adelicFiniteBlockPairCarrier f v) (adelicFiniteFamilyAwayCore f v)
    (AdelicFiniteLocalTensor f v) (adelicFiniteFamilyAwayCore f v)
    inferInstance inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    inferInstance inferInstance inferInstance (adelicFiniteFamilyAwayCoreInner f v)
    (finiteHilbertTensorAssociation (fun i => adelicLocalInnerCarrier f (v i))) LinearIsometry.id

/-- The original pure orbit vectors in the two local blocks, tensored with the same genuine complement. -/
def adelicFiniteBlockedFamily
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ))
    (h : ∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) : AdelicFiniteBlockedTensor f v :=
  (adelicFiniteLocalTensorFamily f (fun i : Fin n => v (Fin.castAdd m i)) g ⊗ₜ[ℂ]
    adelicFiniteLocalTensorFamily f (fun j : Fin m => v (Fin.natAdd n j)) h) ⊗ₜ[ℂ]
      adelicFiniteFamilyAwayOrbit f v a

/-- Genuine tensor grouping concatenates precisely the actual local orbit coordinates and leaves the complement unchanged. -/
theorem adelicFiniteTensorAssociation_family
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ))
    (h : ∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteTensorAssociation f v (adelicFiniteBlockedFamily f v g h a) =
      adelicFiniteFullTensorFamily f v (Fin.addCases g h, a) := by
  have hlocal := finiteHilbertTensorAssociation_pure (fun i => adelicLocalInnerCarrier f (v i))
    (fun i : Fin n => adelicLocalUnitOrbit f (v (Fin.castAdd m i)) (g i))
    (fun j : Fin m => adelicLocalUnitOrbit f (v (Fin.natAdd n j)) (h j))
  have ht : Fin.addCases
      (fun i : Fin n => adelicLocalUnitOrbit f (v (Fin.castAdd m i)) (g i))
      (fun j : Fin m => adelicLocalUnitOrbit f (v (Fin.natAdd n j)) (h j)) =
      (fun i => adelicLocalUnitOrbit f (v i) (Fin.addCases g h i)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
    · simp only [Fin.addCases_right]
  have hl := hlocal.trans (congrArg (finiteHilbertPureTensor (fun i => adelicLocalInnerCarrier f (v i))) ht)
  change TensorProduct.map (finiteHilbertTensorAssociation (fun i => adelicLocalInnerCarrier f (v i))).toLinearMap
    LinearMap.id ((adelicFiniteLocalTensorFamily f (fun i : Fin n => v (Fin.castAdd m i)) g ⊗ₜ[ℂ]
      adelicFiniteLocalTensorFamily f (fun j : Fin m => v (Fin.natAdd n j)) h) ⊗ₜ[ℂ]
        adelicFiniteFamilyAwayOrbit f v a) = _
  rw [TensorProduct.map_tmul]
  exact congrArg (fun x => x ⊗ₜ[ℂ] adelicFiniteFamilyAwayOrbit f v a) hl

variable (F : PrimitiveCuspForm N k)

/-- Every genuinely grouped original orbit tensor realizes the literal product of the original adjacent adelic blocks and complement. -/
theorem adelicFiniteTensorAssociation_original_orbit (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (g : ∀ i : Fin n, GeneralLinearGroup (Fin 2) ((v (Fin.castAdd m i)).adicCompletion ℚ))
    (h : ∀ j : Fin m, GeneralLinearGroup (Fin 2) ((v (Fin.natAdd n j)).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullTensorIsometry F v hv hgood
      (adelicFiniteTensorAssociation F.toCuspForm v (adelicFiniteBlockedFamily F.toCuspForm v g h a)) =
      adelicCyclicHilbertRepresentation F.toCuspForm
        (adelicFinitePlaceProduct (fun i : Fin n => v (Fin.castAdd m i)) (adelicPlaceFamily_left_injective v hv) g *
          adelicFinitePlaceProduct (fun j : Fin m => v (Fin.natAdd n j)) (adelicPlaceFamily_right_injective v hv) h * a.val)
        (adelicCyclicUnitReference F.toCuspForm) := by
  have h₁ := congrArg (adelicFiniteFullTensorIsometry F v hv hgood)
    (adelicFiniteTensorAssociation_family F.toCuspForm v g h a)
  have h₂ := adelicFiniteFullTensorIsometry_family F v hv hgood (Fin.addCases g h, a)
  have hG := congrArg (fun c : RationalAdelicGL2 => c * a.val) (adelicFinitePlaceProduct_addCases v hv g h)
  have h₃ := congrArg (fun c => adelicCyclicHilbertRepresentation F.toCuspForm c
    (adelicCyclicUnitReference F.toCuspForm)) hG
  exact h₁.trans (h₂.trans h₃)

end
end Dubon2026
