import Dubon2026.AdelicLocalAwayTensor

/-! # The genuine local-away tensor map has exactly the original finite-adelic orbit span as its image -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine mixed family is exactly its original finite-adelic product translate with the prescribed original norm factor. -/
theorem adelicLocalAwayMixedFamily_eq_finite (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v) :
    adelicLocalAwayMixedFamily f v a = (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
      adelicCyclicHilbertRepresentation f
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v a.1 * a.2.val))
          (adelicCyclicHilbertGenerator f) := by
  have he := @representation_hom_mul_apply
    (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v a.1) a.2.val (adelicCyclicHilbertGenerator f)
  exact congrArg (fun x : AdelicCyclicHilbert f => (‖adelicCyclicHilbertGenerator f‖ : ℂ) • x) he.symm

/-- Every genuine mixed local-away orbit vector is an actual finite-adelic cusp orbit combination. -/
theorem adelicLocalAwayMixedFamily_mem_finite (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × finiteAdelicAwayGroup v) :
    adelicLocalAwayMixedFamily f v a ∈ adelicFiniteCyclicSpan f := by
  rw [adelicLocalAwayMixedFamily_eq_finite]
  exact (adelicFiniteCyclicSpan f).smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Actual removal of one finite coordinate proves that the genuine mixed family spans the entire original finite-adelic algebraic core. -/
theorem adelicLocalAwayMixedFamily_span (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    Submodule.span ℂ (Set.range (adelicLocalAwayMixedFamily f v)) = adelicFiniteCyclicSpan f := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adelicLocalAwayMixedFamily_mem_finite f v a
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    let a : finiteAdelicAwayGroup v := ⟨finiteAdelicPlaceRemoval v b, finiteAdelicPlaceRemoval_same v b⟩
    let g := GeneralLinearGroup.map (finiteAdelePlace v) b
    have he : adelicLocalAwayMixedFamily f v (g, a) =
        (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
          adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b)
            (adelicCyclicHilbertGenerator f) := by
      rw [adelicLocalAwayMixedFamily_eq_finite]
      change (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
        adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding
          (finiteAdelicLocalGL2 v (GeneralLinearGroup.map (finiteAdelePlace v) b) * finiteAdelicPlaceRemoval v b))
          (adelicCyclicHilbertGenerator f) = _
      rw [finiteAdelicLocal_mul_removal]
    have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf))
    have hs : adelicLocalAwayMixedFamily f v (g, a) ∈
        Submodule.span ℂ (Set.range (adelicLocalAwayMixedFamily f v)) :=
      Submodule.subset_span ⟨(g, a), rfl⟩
    rw [he] at hs
    exact ((Submodule.span ℂ (Set.range (adelicLocalAwayMixedFamily f v))).smul_mem_iff hn).mp hs

/-- The actual local-away tensor isometry has precisely the original finite-adelic algebraic cusp span as its image. -/
theorem adelicLocalAwayTensorIsometry_range {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalAwayTensorIsometry F hpN).toLinearMap.range = adelicFiniteCyclicSpan F.toCuspForm := by
  rw [adelicLocalAwayTensorIsometry, gramSpanningIsometry_range,
    adelicLocalAwayMixedFamily_span F.toCuspForm (primitiveCuspForm_ne_zero F)]

/-- The genuine local-away tensor image is dense in the entire original lowest-weight Hilbert space. -/
theorem adelicLocalAwayTensorIsometry_range_closure {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hk : 0 < k) (hpN : p.Coprime N) :
    (adelicLocalAwayTensorIsometry F hpN).toLinearMap.range.topologicalClosure =
      adelicRotationWeightSpace F.toCuspForm := by
  rw [adelicLocalAwayTensorIsometry_range F hpN, adelicFiniteCyclicSpan_closure,
    ← adelicRotationWeightSpace_eq_finiteClosure F.toCuspForm (primitiveCuspForm_ne_zero F) hk]

end
end Dubon2026
