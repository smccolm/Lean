import Dubon2026.AdelicFiniteTensorIsometry

/-! # The actual finite-family tensor image is precisely the original full adelic cyclic core -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}

/-- Nonzero normalization and the genuine finite-family group equivalence give exactly the original full algebraic cusp orbit span. -/
theorem adelicFiniteFullMixedFamily_span (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : f ≠ 0) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v) :
    Submodule.span ℂ (Set.range (adelicFiniteFullMixedFamily f v hv)) =
      Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f))) := by
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he : adelicFiniteFullMixedFamily f v hv = fun b => (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ •
      adelicCyclicHilbertRepresentation f (adelicFiniteFamilyEquiv v hv b) (adelicCyclicHilbertGenerator f) := by
    funext b
    exact map_smul (adelicCyclicHilbertRepresentation f (adelicFiniteFamilyEquiv v hv b)) _ _
  rw [he]
  exact @scaled_reindexed_orbit_span RationalAdelicGL2
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f) (adelicCyclicHilbertGenerator f)
    (adelicFiniteFamilyEquiv v hv) _ hn

variable (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- The genuine finite tensor isometry has exactly the original full adelic algebraic cusp orbit span as its range. -/
theorem adelicFiniteFullTensorIsometry_range (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap.range =
      Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation F.toCuspForm g (adelicCyclicHilbertGenerator F.toCuspForm))) := by
  rw [adelicFiniteFullTensorIsometry, gramSpanningIsometry_range]
  exact adelicFiniteFullMixedFamily_span F.toCuspForm (primitiveCuspForm_ne_zero F) v hv

/-- The image of the actual finite-family tensor is dense in the entire original full adelic Hilbert space. -/
theorem adelicFiniteFullTensorIsometry_range_closure (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    (adelicFiniteFullTensorIsometry F v hv hgood).toLinearMap.range.topologicalClosure = ⊤ := by
  rw [adelicFiniteFullTensorIsometry_range F v hv hgood]
  apply SetLike.coe_injective
  exact adelicCyclicHilbertGenerator_cyclic F.toCuspForm

end
end Dubon2026
