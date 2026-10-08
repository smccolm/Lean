import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! # Exact scalar action on the genuine closure of an original cyclic family -/

namespace Dubon2026

/-- A bounded operator with the same scalar on all original generators has that scalar on their whole actual closed span. -/
theorem continuousLinearMap_scalar_on_closedSpan {V ι : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (T : V →L[ℂ] V) (a : ℂ) (v : ι → V)
    (hi : ∀ i, T (v i) = a • v i) (w : V)
    (hw : w ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) : T w = a • w := by
  have hs : ∀ u ∈ Submodule.span ℂ (Set.range v), T u = a • u := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hi i
    | zero => simp only [map_zero, smul_zero]
    | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, smul_add]
    | smul c x hx ih => simp only [map_smul, ih, smul_comm c a]
  exact closure_minimal hs (isClosed_eq T.continuous (continuous_const.smul continuous_id)) hw

end Dubon2026
