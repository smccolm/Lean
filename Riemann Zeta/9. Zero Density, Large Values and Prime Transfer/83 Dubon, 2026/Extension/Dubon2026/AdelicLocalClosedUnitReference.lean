import Dubon2026.AdelicLocalUnitOrbit
import Dubon2026.ClosedSpanFamilyDensity
import Dubon2026.AdelicLocalCyclicProjection

/-! # The genuine unit cyclic vector in the original closed local Hilbert factor -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The closed original local factor retains exactly the original ambient Hilbert inner product. -/
instance adelicLocalCyclicClosedSpanInnerProduct (v : HeightOneSpectrum ℤ) :
    InnerProductSpace ℂ (adelicLocalCyclicClosedSpan f v) :=
  @Submodule.innerProductSpace ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance _

/-- Addition is continuous in the actual inherited local Hilbert topology. -/
instance adelicLocalCyclicClosedSpan_continuousAdd (v : HeightOneSpectrum ℤ) :
    ContinuousAdd (adelicLocalCyclicClosedSpan f v) where
  continuous_add := by
    have ha : Continuous (fun x : adelicLocalCyclicClosedSpan f v × adelicLocalCyclicClosedSpan f v =>
        x.1.val + x.2.val) :=
      (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)
    exact ha.subtype_mk _

/-- Scalar multiplication is continuous in the actual inherited local topology. -/
instance adelicLocalCyclicClosedSpan_continuousConstSMul (v : HeightOneSpectrum ℤ) :
    ContinuousConstSMul ℂ (adelicLocalCyclicClosedSpan f v) where
  continuous_const_smul c := by
    have hc : Continuous (fun x : AdelicCyclicHilbert f => c • x) := continuous_const_smul c
    exact (hc.comp continuous_subtype_val).subtype_mk _

/-- The literal original unit reference belongs to the actual closed local orbit factor. -/
def adelicLocalClosedUnitReference (v : HeightOneSpectrum ℤ) : adelicLocalCyclicClosedSpan f v :=
  (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ •
    ⟨adelicCyclicHilbertGenerator f, adelicLocalCyclicClosedSpan_generator_mem f v⟩

/-- The closed local unit reference is the original ambient unit reference without a changed normalization. -/
theorem adelicLocalClosedUnitReference_val (v : HeightOneSpectrum ℤ) :
    (adelicLocalClosedUnitReference f v).val = adelicCyclicUnitReference f := rfl

/-- The original nonzero cusp form gives a genuine unit vector in its actual local Hilbert factor. -/
theorem adelicLocalClosedUnitReference_inner (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    inner ℂ (adelicLocalClosedUnitReference f v) (adelicLocalClosedUnitReference f v) = 1 := by
  have hn : ‖adelicLocalClosedUnitReference f v‖ = 1 := adelicCyclicUnitReference_norm f hf
  rw [inner_self_eq_norm_sq_to_K, hn]
  norm_num

/-- The actual restricted original local representation preserves its inherited Hilbert inner product. -/
theorem adelicLocalCyclicRepresentation_inner (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x y : adelicLocalCyclicClosedSpan f v) :
    inner ℂ (adelicLocalCyclicRepresentation f v g x) (adelicLocalCyclicRepresentation f v g y) = inner ℂ x y :=
  adelicCyclicLocalRepresentation_inner f v g x.val y.val

/-- Every actual central scalar acts trivially on the genuine closed local factor. -/
theorem adelicLocalCyclicRepresentation_scalar (v : HeightOneSpectrum ℤ)
    (u : (v.adicCompletion ℚ)ˣ) (x : adelicLocalCyclicClosedSpan f v) :
    adelicLocalCyclicRepresentation f v (GeneralLinearGroup.scalar (Fin 2) u) x = x :=
  Subtype.ext (adelicCyclicLocal_scalar_action f v u x.val)

/-- The orbit of the original unit reference densely spans the entire actual original closed local factor. -/
theorem adelicLocalClosedUnitReference_cyclic (hf : f ≠ 0) (v : HeightOneSpectrum ℤ) :
    (Submodule.span ℂ (Set.range (fun g =>
      adelicLocalCyclicRepresentation f v g (adelicLocalClosedUnitReference f v)))).topologicalClosure = ⊤ := by
  apply @closedSpan_subtype_family_dense
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (AdelicCyclicHilbert f)
    inferInstance inferInstance (adelicLocalCyclicClosedSpan f v)
    (fun g => adelicLocalCyclicRepresentation f v g (adelicLocalClosedUnitReference f v))
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have hs := @scaled_reindexed_orbit_span
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation f v) (adelicCyclicHilbertGenerator f) (MulEquiv.refl _) _ hn
  have he : Submodule.span ℂ (Set.range (fun g =>
      (adelicLocalCyclicRepresentation f v g (adelicLocalClosedUnitReference f v)).val)) =
      Submodule.span ℂ (Set.range (fun g => adelicCyclicLocalRepresentation f v g (adelicCyclicHilbertGenerator f))) := by
    simpa only [adelicLocalCyclicRepresentation_apply, adelicLocalClosedUnitReference,
      Submodule.coe_smul, map_smul, MulEquiv.refl_apply] using hs
  exact congrArg Submodule.topologicalClosure he

end
end Dubon2026
