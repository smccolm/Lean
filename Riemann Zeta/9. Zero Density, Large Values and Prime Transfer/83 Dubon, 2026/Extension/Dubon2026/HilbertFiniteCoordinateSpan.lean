import Mathlib.Analysis.InnerProductSpace.l2Space

/-! # Actual finite Hilbert support is precisely finite algebraic basis expansion -/

namespace Dubon2026

noncomputable section

/-- A vector with finitely many nonzero actual Hilbert coordinates belongs to the original algebraic basis span. -/
theorem hilbertBasis_mem_span_of_finite_coordinates {V ι : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (b : HilbertBasis ι ℂ V) (v : V)
    (h : Set.Finite {i | b.repr v i ≠ 0}) : v ∈ Submodule.span ℂ (Set.range b) := by
  classical
  have hs : HasSum (fun i => b.repr v i • b i) (∑ i ∈ h.toFinset, b.repr v i • b i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro i hi
    have hz : b.repr v i = 0 := by simpa using hi
    rw [hz, zero_smul]
  rw [(b.hasSum_repr v).unique hs]
  exact Submodule.sum_mem _ (fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end
end Dubon2026
