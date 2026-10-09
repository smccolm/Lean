import Dubon2026.AdelicRestrictedTensorDirectLimit
import Dubon2026.AdelicRestrictedFiniteOrbitCoverage
import Dubon2026.AdelicFiniteTensorRange

/-! # Density of the genuine restricted algebraic tensor in the original cusp Hilbert space -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The normalized original cusp reference has exactly the same algebraic full adelic orbit span as the original generator. -/
theorem adelicCyclicUnitReference_span (hf : f ≠ 0) :
    Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f))) =
      Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
        adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertGenerator f))) := by
  have hn : (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact_mod_cast norm_ne_zero_iff.mpr (adelicCyclicHilbertGenerator_ne_zero f hf)
  have he : (fun a : RationalAdelicGL2 => adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f)) =
      fun a => (‖adelicCyclicHilbertGenerator f‖ : ℂ)⁻¹ •
        adelicCyclicHilbertRepresentation f a (adelicCyclicHilbertGenerator f) := by
    funext a
    exact map_smul (adelicCyclicHilbertRepresentation f a) _ _
  rw [he]
  exact scaled_reindexed_orbit_span (adelicCyclicHilbertRepresentation f) (adelicCyclicHilbertGenerator f)
    (MulEquiv.refl RationalAdelicGL2) _ hn

/-- The actual normalized original adelic orbit spans a dense subspace of the entire original Hilbert space. -/
theorem adelicCyclicUnitReference_span_closure (hf : f ≠ 0) :
    (Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f a (adelicCyclicUnitReference f)))).topologicalClosure = ⊤ := by
  rw [adelicCyclicUnitReference_span f hf]
  apply SetLike.coe_injective
  exact adelicCyclicHilbertGenerator_cyclic f

variable (F : PrimitiveCuspForm N k)

/-- Every actual original unit-reference orbit vector belongs to the range of the genuine restricted algebraic tensor. -/
theorem adelicRestrictedAlgebraicTensorIsometry_orbit_mem (a : RationalAdelicGL2) :
    adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm) ∈
      (adelicRestrictedAlgebraicTensorIsometry F).toLinearMap.range :=
  (adelicRestrictedAlgebraicTensorIsometry_mem_range_iff F _).mpr
    (adelicRestrictedStageIsometry_covers_original_orbit F a)

/-- The actual genuine restricted tensor image is dense in the entire original adelic cusp Hilbert space. -/
theorem adelicRestrictedAlgebraicTensorIsometry_range_closure :
    (adelicRestrictedAlgebraicTensorIsometry F).toLinearMap.range.topologicalClosure = ⊤ := by
  have hs : Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm))) ≤
      (adelicRestrictedAlgebraicTensorIsometry F).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adelicRestrictedAlgebraicTensorIsometry_orbit_mem F a
  apply top_unique
  rw [← adelicCyclicUnitReference_span_closure F.toCuspForm (primitiveCuspForm_ne_zero F)]
  exact Submodule.topologicalClosure_mono hs

end
end Dubon2026
