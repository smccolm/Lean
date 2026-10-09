import Dubon2026.AdelicLocalFullMixedCoefficient
import Dubon2026.AdelicLocalAwayTensor
import Dubon2026.GramSpanningIsometry
import Dubon2026.TensorOrbitSpanning

/-! # A genuine algebraic tensor isometry for the original local and real-plus-away orbit spans -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal algebraic span of the genuine real-plus-away orbit of the original cusp generator. -/
def adelicFullAwayCyclicCore (v : HeightOneSpectrum ℤ) : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun a : AdelicFullAwayGroup v =>
    adelicCyclicFullAwayRepresentation f v a (adelicCyclicHilbertGenerator f)))

/-- The actual real-plus-away algebraic orbit core inherits the original Hilbert inner product. -/
instance adelicFullAwayCyclicCoreInnerProduct (v : HeightOneSpectrum ℤ) :
    InnerProductSpace ℂ (adelicFullAwayCyclicCore f v) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicFullAwayCyclicCore f v)

/-- The actual algebraic tensor product carries the genuine Hilbert tensor norm from the two inherited inner products. -/
instance adelicLocalFullAwayTensorNormed (v : HeightOneSpectrum ℤ) :
    NormedAddCommGroup (adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v) :=
  @TensorProduct.instNormedAddCommGroup ℂ (adelicLocalCyclicCore f v) (adelicFullAwayCyclicCore f v)
    inferInstance inferInstance (adelicLocalCyclicCoreInnerProduct f v)
    inferInstance (adelicFullAwayCyclicCoreInnerProduct f v)

/-- The genuine tensor inner product is exactly the product inner product on original pure orbit tensors. -/
instance adelicLocalFullAwayTensorInnerProduct (v : HeightOneSpectrum ℤ) :
    InnerProductSpace ℂ (adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v) :=
  @TensorProduct.instInnerProductSpace ℂ (adelicLocalCyclicCore f v) (adelicFullAwayCyclicCore f v)
    inferInstance inferInstance (adelicLocalCyclicCoreInnerProduct f v)
    inferInstance (adelicFullAwayCyclicCoreInnerProduct f v)

/-- The actual pure tensors of the original local and real-plus-away cusp orbit vectors. -/
def adelicLocalFullAwayTensorFamily (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) :
    adelicLocalCyclicCore f v ⊗[ℂ] adelicFullAwayCyclicCore f v :=
  (⟨adelicCyclicLocalRepresentation f v a.1 (adelicCyclicHilbertGenerator f),
    Submodule.subset_span ⟨a.1, rfl⟩⟩ : adelicLocalCyclicCore f v) ⊗ₜ[ℂ]
  (⟨adelicCyclicFullAwayRepresentation f v a.2 (adelicCyclicHilbertGenerator f),
    Submodule.subset_span ⟨a.2, rfl⟩⟩ : adelicFullAwayCyclicCore f v)

/-- The genuine mixed orbit with the original generator norm giving exactly the tensor inner-product normalization. -/
def adelicLocalFullAwayMixedFamily (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) : AdelicCyclicHilbert f :=
  (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
    adelicCyclicLocalRepresentation f v a.1
      (adelicCyclicFullAwayRepresentation f v a.2 (adelicCyclicHilbertGenerator f))

/-- Tensors of the actual orbit vectors span the entire genuine algebraic tensor product of the two original cores. -/
theorem adelicLocalFullAwayTensorFamily_span (v : HeightOneSpectrum ℤ) :
    Submodule.span ℂ (Set.range (adelicLocalFullAwayTensorFamily f v)) = ⊤ := by
  let u : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) → adelicLocalCyclicCore f v :=
    fun g => ⟨adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f),
      Submodule.subset_span ⟨g, rfl⟩⟩
  let w : AdelicFullAwayGroup v → adelicFullAwayCyclicCore f v :=
    fun a => ⟨adelicCyclicFullAwayRepresentation f v a (adelicCyclicHilbertGenerator f),
      Submodule.subset_span ⟨a, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (adelicLocalCyclicCore f v) _).mpr rfl
  have hw : Submodule.span ℂ (Set.range w) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (adelicFullAwayCyclicCore f v) _).mpr rfl
  exact @tensorFamily_span_eq_top
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (AdelicFullAwayGroup v)
    (adelicLocalCyclicCore f v) (adelicFullAwayCyclicCore f v)
    inferInstance inferInstance inferInstance inferInstance u w hu hw

/-- The original mixed Gram identity gives exactly the genuine tensor-product Gram matrix, with its original norm normalization. -/
theorem adelicLocalFullAwayTensorFamily_gram {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (a b : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    inner ℂ (adelicLocalFullAwayTensorFamily F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a)
      (adelicLocalFullAwayTensorFamily F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b) =
    inner ℂ (adelicLocalFullAwayMixedFamily F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a)
      (adelicLocalFullAwayMixedFamily F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b) := by
  have he := (adelicCyclicLocal_fullAway_mixed_gram F hpN a.1 b.1 a.2 b.2).symm
  have hn := @norm_smul_inner_factor (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance
    (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a.1
      (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a.2
        (adelicCyclicHilbertGenerator F.toCuspForm)))
    (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b.1
      (adelicCyclicFullAwayRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) b.2
        (adelicCyclicHilbertGenerator F.toCuspForm)))
  exact he.trans hn.symm

/-- A genuine linear isometry from the actual tensor product of original local and real-plus-away algebraic orbit cores into the original adelic Hilbert space. -/
def adelicLocalFullAwayTensorIsometry {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗[ℂ]
      adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) →ₗᵢ[ℂ]
      AdelicCyclicHilbert F.toCuspForm :=
  gramSpanningIsometry (adelicLocalFullAwayTensorFamily F.toCuspForm _)
    (adelicLocalFullAwayMixedFamily F.toCuspForm _) (adelicLocalFullAwayTensorFamily_gram F hpN)
    (adelicLocalFullAwayTensorFamily_span F.toCuspForm _)

/-- The original tensor isometry sends every actual local/full-complement pure orbit tensor to its exact genuine mixed cusp vector. -/
theorem adelicLocalFullAwayTensorIsometry_family {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (a : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) ×
      AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalFullAwayTensorFamily F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a) =
    adelicLocalFullAwayMixedFamily F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) a :=
  gramSpanningIsometry_family _ _ _ _ a

end
end Dubon2026
