import Dubon2026.AdelicTensorUnitReference

/-! # Tensor reference inclusions recover the actual original local and complementary vectors -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] [Fact p.Prime]
  (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

/-- Tensoring any original local core vector with the genuine complementary unit reference recovers that exact original vector. -/
theorem adelicLocalFullAwayTensorIsometry_right_reference
    (x : adelicLocalCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (x ⊗ₜ[ℂ] adelicFullAwayUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
        x.val := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  let u : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) → adelicLocalCyclicCore F.toCuspForm v :=
    fun g => ⟨adelicCyclicLocalRepresentation F.toCuspForm v g (adelicCyclicHilbertGenerator F.toCuspForm),
      Submodule.subset_span ⟨g, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (adelicLocalCyclicCore F.toCuspForm v) _).mpr rfl
  have hn : (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr
      (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F))
  apply @tensorMap_right_inverse_reference
    (adelicLocalCyclicCore F.toCuspForm v) (adelicFullAwayCyclicCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) u hu
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap
    (adelicLocalCyclicCore F.toCuspForm v).subtype
    ⟨adelicCyclicHilbertGenerator F.toCuspForm, adelicFullAwayCyclicCore_generator_mem F.toCuspForm v⟩
    (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) hn _ x
  intro g
  have hb := adelicLocalFullAwayTensorIsometry_family F hpN (g, 1)
  simpa only [adelicLocalFullAwayTensorFamily, adelicLocalFullAwayMixedFamily,
    map_one, Module.End.one_apply] using hb

/-- Tensoring the genuine local unit reference with any original full-complement core vector recovers that exact original vector. -/
theorem adelicLocalFullAwayTensorIsometry_left_reference
    (x : adelicFullAwayCyclicCore F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicLocalFullAwayTensorIsometry F hpN
      (adelicLocalUnitReference F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)) ⊗ₜ[ℂ] x) =
        x.val := by
  let v := rationalPrimePlace p (Fact.out : p.Prime)
  let u : AdelicFullAwayGroup v → adelicFullAwayCyclicCore F.toCuspForm v :=
    fun g => ⟨adelicCyclicFullAwayRepresentation F.toCuspForm v g (adelicCyclicHilbertGenerator F.toCuspForm),
      Submodule.subset_span ⟨g, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (adelicFullAwayCyclicCore F.toCuspForm v) _).mpr rfl
  have hn : (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr
      (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F))
  apply @tensorMap_left_inverse_reference
    (adelicLocalCyclicCore F.toCuspForm v) (adelicFullAwayCyclicCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (AdelicFullAwayGroup v) u hu
    (adelicLocalFullAwayTensorIsometry F hpN).toLinearMap
    (adelicFullAwayCyclicCore F.toCuspForm v).subtype
    ⟨adelicCyclicHilbertGenerator F.toCuspForm, adelicLocalCyclicCore_generator_mem F.toCuspForm v⟩
    (‖adelicCyclicHilbertGenerator F.toCuspForm‖ : ℂ) hn _ x
  intro g
  have hb := adelicLocalFullAwayTensorIsometry_family F hpN (1, g)
  simpa only [adelicLocalFullAwayTensorFamily, adelicLocalFullAwayMixedFamily,
    map_one, Module.End.one_apply] using hb

end
end Dubon2026
