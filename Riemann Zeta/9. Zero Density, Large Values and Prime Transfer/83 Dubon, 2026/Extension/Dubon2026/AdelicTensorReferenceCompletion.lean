import Dubon2026.AdelicTensorReferenceInclusion
import Dubon2026.LinearIsometryCompletionFunctor

/-! # Genuine completed reference inclusions agree with the original local and complementary Hilbert embeddings -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The completed local core has the genuine normed additive structure of its completion. -/
instance adelicLocalCyclicCompletionNormed (v : HeightOneSpectrum ℤ) :
    NormedAddCommGroup (Completion (adelicLocalCyclicCore f v)) :=
  @Completion.instNormedAddCommGroup (adelicLocalCyclicCore f v) inferInstance

/-- The additive structure is exactly the one inherited from the actual completed local normed group. -/
instance adelicLocalCyclicCompletionAddGroup (v : HeightOneSpectrum ℤ) :
    AddCommGroup (Completion (adelicLocalCyclicCore f v)) :=
  (adelicLocalCyclicCompletionNormed f v).toAddCommGroup

/-- The local completion carries the genuine completed original inner product. -/
instance adelicLocalCyclicCompletionInner (v : HeightOneSpectrum ℤ) :
    InnerProductSpace ℂ (Completion (adelicLocalCyclicCore f v)) :=
  @Completion.innerProductSpace ℂ (adelicLocalCyclicCore f v) inferInstance inferInstance
    (adelicLocalCyclicCoreInnerProduct f v)

/-- The local completion's scalar action is exactly the action inherited from its completed inner product. -/
instance adelicLocalCyclicCompletionModule (v : HeightOneSpectrum ℤ) :
    Module ℂ (Completion (adelicLocalCyclicCore f v)) :=
  (adelicLocalCyclicCompletionInner f v).toNormedSpace.toModule

/-- The completed complementary core has the genuine normed additive structure of its completion. -/
instance adelicFullAwayCyclicCompletionNormed (v : HeightOneSpectrum ℤ) :
    NormedAddCommGroup (Completion (adelicFullAwayCyclicCore f v)) :=
  @Completion.instNormedAddCommGroup (adelicFullAwayCyclicCore f v) inferInstance

/-- The additive structure is exactly the one inherited from the actual completed complementary normed group. -/
instance adelicFullAwayCyclicCompletionAddGroup (v : HeightOneSpectrum ℤ) :
    AddCommGroup (Completion (adelicFullAwayCyclicCore f v)) :=
  (adelicFullAwayCyclicCompletionNormed f v).toAddCommGroup

/-- The complementary completion carries the genuine completed original inner product. -/
instance adelicFullAwayCyclicCompletionInner (v : HeightOneSpectrum ℤ) :
    InnerProductSpace ℂ (Completion (adelicFullAwayCyclicCore f v)) :=
  @Completion.innerProductSpace ℂ (adelicFullAwayCyclicCore f v) inferInstance inferInstance
    (adelicFullAwayCyclicCoreInnerProduct f v)

/-- The complementary completion's scalar action is exactly the action inherited from its completed inner product. -/
instance adelicFullAwayCyclicCompletionModule (v : HeightOneSpectrum ℤ) :
    Module ℂ (Completion (adelicFullAwayCyclicCore f v)) :=
  (adelicFullAwayCyclicCompletionInner f v).toNormedSpace.toModule

/-- The actual completed local factor embeds into the original completed tensor by the complementary unit reference. -/
def adelicLocalReferenceCompletionInclusion (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    Completion (adelicLocalCyclicCore f v) →ₗᵢ[ℂ] AdelicLocalFullAwayHilbertTensor f v :=
  @linearIsometryCompletionFunctor (adelicLocalCyclicCore f v)
    (adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v)
    inferInstance inferInstance inferInstance inferInstance
    (@tensorUnitRight (adelicLocalCyclicCore f v) (adelicFullAwayCyclicCore f v)
      inferInstance inferInstance inferInstance inferInstance
      (adelicFullAwayUnitReference f v) (adelicFullAwayUnitReference_norm f hf v))

/-- The actual completed complementary factor embeds by the genuine local unit reference. -/
def adelicFullAwayReferenceCompletionInclusion (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    Completion (adelicFullAwayCyclicCore f v) →ₗᵢ[ℂ] AdelicLocalFullAwayHilbertTensor f v :=
  @linearIsometryCompletionFunctor (adelicFullAwayCyclicCore f v)
    (adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v)
    inferInstance inferInstance inferInstance inferInstance
    (@tensorUnitLeft (adelicLocalCyclicCore f v) (adelicFullAwayCyclicCore f v)
      inferInstance inferInstance inferInstance inferInstance
      (adelicLocalUnitReference f v) (adelicLocalUnitReference_norm f hf v))

/-- On original local vectors the completed inclusion is exactly the pure tensor with the actual unit reference. -/
theorem adelicLocalReferenceCompletionInclusion_coe (hf : f ≠ 0) (v : HeightOneSpectrum ℤ)
    (x : adelicLocalCyclicCore f v) :
    adelicLocalReferenceCompletionInclusion f hf v (x : Completion (adelicLocalCyclicCore f v)) =
      (x ⊗ₜ[ℂ] adelicFullAwayUnitReference f v : AdelicLocalFullAwayHilbertTensor f v) :=
  linearIsometryCompletionFunctor_coe _ x

/-- On original complementary vectors the completed inclusion is the pure tensor with the genuine local reference. -/
theorem adelicFullAwayReferenceCompletionInclusion_coe (hf : f ≠ 0) (v : HeightOneSpectrum ℤ)
    (x : adelicFullAwayCyclicCore f v) :
    adelicFullAwayReferenceCompletionInclusion f hf v (x : Completion (adelicFullAwayCyclicCore f v)) =
      (adelicLocalUnitReference f v ⊗ₜ[ℂ] x : AdelicLocalFullAwayHilbertTensor f v) :=
  linearIsometryCompletionFunctor_coe _ x

variable {p : ℕ} [NeZero p] [Fact p.Prime] (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

/-- Completing the actual right reference inclusion recovers precisely the original local cyclic Hilbert embedding. -/
theorem adelicLocalFullAwayHilbertTensorIsometry_right_reference
    (x : Completion (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN
      (adelicLocalReferenceCompletionInclusion F.toCuspForm (primitiveCuspForm_ne_zero F)
        (rationalPrimePlace p (Fact.out : p.Prime)) x) =
      @linearIsometryCompletion
        (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
        (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
        (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtypeₗᵢ x :=
  @linearIsometryCompletion_diagram
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@tensorUnitRight
      (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      inferInstance inferInstance inferInstance inferInstance
      (adelicFullAwayUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicFullAwayUnitReference_norm F.toCuspForm (primitiveCuspForm_ne_zero F) _))
    (adelicLocalFullAwayTensorIsometry F hpN)
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtypeₗᵢ
    (adelicLocalFullAwayTensorIsometry_right_reference F hpN) x

/-- Completing the actual left reference inclusion recovers precisely the original full-complement cyclic Hilbert embedding. -/
theorem adelicLocalFullAwayHilbertTensorIsometry_left_reference
    (x : Completion (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) :
    adelicLocalFullAwayHilbertTensorIsometry F hpN
      (adelicFullAwayReferenceCompletionInclusion F.toCuspForm (primitiveCuspForm_ne_zero F)
        (rationalPrimePlace p (Fact.out : p.Prime)) x) =
      @linearIsometryCompletion
        (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
        (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
        (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtypeₗᵢ x :=
  @linearIsometryCompletion_diagram
    (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (@tensorUnitLeft
      (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      inferInstance inferInstance inferInstance inferInstance
      (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalUnitReference_norm F.toCuspForm (primitiveCuspForm_ne_zero F) _))
    (adelicLocalFullAwayTensorIsometry F hpN)
    (adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).subtypeₗᵢ
    (adelicLocalFullAwayTensorIsometry_left_reference F hpN) x

end
end Dubon2026
