import Mathlib.Analysis.InnerProductSpace.Orthogonal

/-! # Orthogonality to every original generator forces zero in the actual closed span -/

namespace Dubon2026

/-- A vector in the genuine closed span which is orthogonal to every original generator is zero. -/
theorem closedSpan_orthogonal_eq_zero {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (v : ι → V) (x : V) (hx : x ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure)
    (hi : ∀ i, inner ℂ x (v i) = 0) : x = 0 := by
  have hs : ∀ y ∈ Submodule.span ℂ (Set.range v), inner ℂ x y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hi i
    | zero => exact inner_zero_right x
    | add a b ha hb iha ihb => simp only [inner_add_right, iha, ihb, add_zero]
    | smul c y hy ih => simp only [inner_smul_right, ih, mul_zero]
  have hclosed : IsClosed {y : V | inner ℂ x y = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact inner_self_eq_zero.mp (closure_minimal hs hclosed hx)

end Dubon2026
