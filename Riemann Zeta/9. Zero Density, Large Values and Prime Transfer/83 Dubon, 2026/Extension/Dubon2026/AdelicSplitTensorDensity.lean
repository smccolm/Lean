import Dubon2026.AdelicSplitTensorDirectLimit
import Dubon2026.AdelicRestrictedTensorDensity

/-! # Density of the actual tensor with every original finite and real factor split -/

namespace Dubon2026

noncomputable section

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- Every original adelic unit-reference orbit is realized by an actual finite tensor of individual local factors. -/
theorem adelicSplitStageIsometry_covers_original_orbit (hk : 0 < k) (a : RationalAdelicGL2) :
    ∃ n x, adelicSplitStageIsometry F hk n x =
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm) := by
  obtain ⟨n, y, hy⟩ := adelicRestrictedStageIsometry_covers_original_orbit F a
  refine ⟨n, (adelicSplitStageEquiv F hk n).symm y, ?_⟩
  exact (congrArg (adelicRestrictedStageIsometry F n)
    ((adelicSplitStageEquiv F hk n).apply_symm_apply y)).trans hy

/-- The original unit-reference adelic orbit belongs to the realized full restricted tensor. -/
theorem adelicSplitAlgebraicTensorIsometry_orbit_mem (hk : 0 < k) (a : RationalAdelicGL2) :
    adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm) ∈
      (adelicSplitAlgebraicTensorIsometry F hk).toLinearMap.range :=
  (adelicSplitAlgebraicTensorIsometry_mem_range_iff F hk _).mpr
    (adelicSplitStageIsometry_covers_original_orbit F hk a)

/-- The independently normed full restricted local tensor has dense image in the whole original adelic Hilbert space. -/
theorem adelicSplitAlgebraicTensorIsometry_range_closure (hk : 0 < k) :
    (adelicSplitAlgebraicTensorIsometry F hk).toLinearMap.range.topologicalClosure = ⊤ := by
  have hs : Submodule.span ℂ (Set.range (fun a : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation F.toCuspForm a (adelicCyclicUnitReference F.toCuspForm))) ≤
      (adelicSplitAlgebraicTensorIsometry F hk).toLinearMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adelicSplitAlgebraicTensorIsometry_orbit_mem F hk a
  apply top_unique
  rw [← adelicCyclicUnitReference_span_closure F.toCuspForm (primitiveCuspForm_ne_zero F)]
  exact Submodule.topologicalClosure_mono hs

end
end Dubon2026
