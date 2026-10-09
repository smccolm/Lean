import Dubon2026.AdelicLocalFullAwayTensor

/-! # The genuine local/full-complement tensor spans the entire original adelic cusp representation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

/-- Nonzero scalar normalization and an actual surjective group reindexing preserve the original algebraic orbit span. -/
theorem scaled_reindexed_orbit_span {G H V : Type*} [Group G] [Group H]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (y : V)
    (e : H ≃* G) (c : ℂ) (hc : c ≠ 0) :
    Submodule.span ℂ (Set.range (fun a => c • ρ (e a) y)) =
      Submodule.span ℂ (Set.range (fun g => ρ g y)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨e a, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    obtain ⟨a, rfl⟩ := e.surjective g
    exact (Submodule.smul_mem_iff _ hc).mp (Submodule.subset_span ⟨a, rfl⟩)

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The true local/full-complement mixed family is precisely the normalized original full adelic orbit. -/
theorem adelicLocalFullAwayMixedFamily_eq_global (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) :
    adelicLocalFullAwayMixedFamily f v a = (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
      adelicCyclicHilbertRepresentation f (adelicLocalFullAwayEquiv v a) (adelicCyclicHilbertGenerator f) := by
  have he := @representation_hom_mul_apply RationalAdelicGL2 RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (MonoidHom.id _) (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v a.1))
    (adelicFullAwayEmbedding v a.2) (adelicCyclicHilbertGenerator f)
  rw [← adelicLocalFullAwayEquiv_factor] at he
  exact congrArg (fun x : AdelicCyclicHilbert f => (‖adelicCyclicHilbertGenerator f‖ : ℂ) • x) he.symm

/-- Actual full complementary coordinates give the entire original full adelic algebraic cyclic span. -/
theorem adelicLocalFullAwayMixedFamily_span (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    Submodule.span ℂ (Set.range (adelicLocalFullAwayMixedFamily f v)) =
      Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation f g (adelicCyclicHilbertGenerator f))) := by
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he : adelicLocalFullAwayMixedFamily f v = fun a => (‖adelicCyclicHilbertGenerator f‖ : ℂ) •
      adelicCyclicHilbertRepresentation f (adelicLocalFullAwayEquiv v a) (adelicCyclicHilbertGenerator f) :=
    funext (adelicLocalFullAwayMixedFamily_eq_global f v)
  rw [he]
  exact @scaled_reindexed_orbit_span RationalAdelicGL2
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v)
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicHilbertRepresentation f) (adelicCyclicHilbertGenerator f)
    (adelicLocalFullAwayEquiv v) _ hn

/-- The true algebraic local/full-complement tensor map has exactly the original full adelic cyclic core as its range. -/
theorem adelicLocalFullAwayTensorIsometry_range {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap.range =
      Submodule.span ℂ (Set.range (fun g : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation F.toCuspForm g (adelicCyclicHilbertGenerator F.toCuspForm))) := by
  rw [adelicLocalFullAwayTensorIsometry, gramSpanningIsometry_range]
  exact adelicLocalFullAwayMixedFamily_span F.toCuspForm (primitiveCuspForm_ne_zero F)
    (rationalPrimePlace p (Fact.out : p.Prime))

/-- The actual local/full-complement tensor image is dense in the entire original full adelic Hilbert representation. -/
theorem adelicLocalFullAwayTensorIsometry_range_closure {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap.range.topologicalClosure = ⊤ := by
  rw [adelicLocalFullAwayTensorIsometry_range F hpN]
  apply SetLike.coe_injective
  exact adelicCyclicHilbertGenerator_cyclic F.toCuspForm

end
end Dubon2026
