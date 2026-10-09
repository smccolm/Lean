import Dubon2026.AdelicTensorUnitReference

/-! # The actual normalized local cusp orbit spans the original local algebraic factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine original local orbit of the actual local unit reference. -/
def adelicLocalUnitOrbit (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) : adelicLocalCyclicCore f v :=
  adelicLocalSmoothRepresentation f v g (adelicLocalUnitReference f v)

/-- Every normalized local orbit vector is literally the corresponding original full adelic translate. -/
theorem adelicLocalUnitOrbit_val (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    (adelicLocalUnitOrbit f v g).val = adelicCyclicHilbertRepresentation f
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicCyclicUnitReference f) := rfl

/-- The actual normalized local orbit has unit norm for every original nonzero cusp form. -/
theorem adelicLocalUnitOrbit_norm (hf : f ≠ 0) (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) : ‖adelicLocalUnitOrbit f v g‖ = 1 := by
  change ‖adelicCyclicHilbertRepresentation f
    (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicCyclicUnitReference f)‖ = 1
  exact (adelicCyclicHilbertOperator_norm f
    (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicCyclicUnitReference f)).trans
    (adelicCyclicUnitReference_norm f hf)

/-- The genuine normalized local cusp orbit spans the entire original local algebraic core. -/
theorem adelicLocalUnitOrbit_span (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    Submodule.span ℂ (Set.range (adelicLocalUnitOrbit f v)) = ⊤ := by
  let y : adelicLocalCyclicCore f v :=
    ⟨adelicCyclicHilbertGenerator f, adelicLocalCyclicCore_generator_mem f v⟩
  have hspan : Submodule.span ℂ (Set.range (fun g => adelicLocalSmoothRepresentation f v g y)) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff (adelicLocalCyclicCore f v) _).mpr rfl
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he := @scaled_reindexed_orbit_span
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (adelicLocalCyclicCore f v) inferInstance inferInstance inferInstance inferInstance
    (adelicLocalSmoothRepresentation f v) y (MulEquiv.refl _) _ hn
  simpa only [MulEquiv.refl_apply, ← map_smul, hspan] using he

end
end Dubon2026
