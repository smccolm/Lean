import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Exact original Gram identities extend from generators to their actual Hilbert closures -/

namespace Dubon2026

noncomputable section

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- An actual continuous mixed Gram factorization on a generating family extends to every pair in its original closed span. -/
theorem continuous_gram_factor_closure (u : ι → E) (T U : E →L[ℂ] F) (c : ℂ)
    (h : ∀ i j, inner ℂ (T (u i)) (U (u j)) = inner ℂ (u i) (u j) * c)
    (x y : E) (hx : x ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure)
    (hy : y ∈ (Submodule.span ℂ (Set.range u)).topologicalClosure) :
    inner ℂ (T x) (U y) = inner ℂ x y * c := by
  have hgen (i : ι) : ∀ z ∈ Submodule.span ℂ (Set.range u),
      inner ℂ (T (u i)) (U z) = inner ℂ (u i) z * c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨j, rfl⟩ := hz; exact h i j
    | zero => simp only [map_zero, inner_zero_right, zero_mul]
    | add z w hz hw ihz ihw => simp only [map_add, inner_add_right, ihz, ihw, add_mul]
    | smul a z hz ih => simp only [map_smul, inner_smul_right, ih, mul_assoc]
  have hgenclosed (i : ι) : inner ℂ (T (u i)) (U y) = inner ℂ (u i) y * c :=
    closure_minimal (hgen i)
      (isClosed_eq (continuous_const.inner U.continuous) ((continuous_const.inner continuous_id).mul continuous_const)) hy
  have hs : ∀ z ∈ Submodule.span ℂ (Set.range u), inner ℂ (T z) (U y) = inner ℂ z y * c := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hgenclosed i
    | zero => simp only [map_zero, inner_zero_left, zero_mul]
    | add z w hz hw ihz ihw => simp only [map_add, inner_add_left, ihz, ihw, add_mul]
    | smul a z hz ih => simp only [map_smul, inner_smul_left, ih, mul_assoc]
  exact closure_minimal hs
    (isClosed_eq (T.continuous.inner continuous_const) ((continuous_id.inner continuous_const).mul continuous_const)) hx

end
end Dubon2026
