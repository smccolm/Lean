import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! # Exact generator line from the genuine orthogonal uniqueness property -/

namespace Dubon2026

/-- If the only vector in two original subspaces orthogonal to their common generator is zero, their intersection is precisely its genuine line. -/
theorem submodule_inf_eq_generator_line {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (P Q : Submodule ℂ V) (y : V) (hyP : y ∈ P) (hyQ : y ∈ Q)
    (hzero : ∀ x, x ∈ P → x ∈ Q → inner ℂ x y = 0 → x = 0) :
    P ⊓ Q = Submodule.span ℂ {y} := by
  let L := Submodule.span ℂ ({y} : Set V)
  have hLP : L ≤ P := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hyP)
  have hLQ : L ≤ Q := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hyQ)
  apply le_antisymm
  · intro x hx
    have hproj := L.starProjection_apply_mem x
    have horth : inner ℂ (x - L.starProjection x) y = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (L.sub_starProjection_mem_orthogonal x)
    have he := hzero (x - L.starProjection x)
      (P.sub_mem hx.1 (hLP hproj)) (Q.sub_mem hx.2 (hLQ hproj)) horth
    exact (sub_eq_zero.mp he).symm ▸ hproj
  · exact le_inf hLP hLQ

end Dubon2026
