import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-! DUB-17/18 -> raw reciprocity -> geometric dissection -> uniform grid scale.
The closed bounded region away from branch disks is compact. The native
Lebesgue-number theorem makes its actual sheet-neighborhood cover uniform,
providing the positive collar needed to fit sufficiently small grid cells.
Adapted from SquareGrid.exists_lebesgue_collar in
S_AlgebraicCurve_exists_dissectionScaleData, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
noncomputable section

theorem exists_lebesgue_collar {R : ℝ} (Branch : Finset ℂ) (s : ℂ → ℝ)
    (Good : Set ℂ → Prop)
    (hcover : ∀ t : ℂ, ‖t‖ ≤ R + 1 → (∀ b ∈ Branch, s b ≤ dist t b) →
      ∃ V, IsOpen V ∧ t ∈ V ∧ Good V) :
    ∃ δ > 0, ∀ t : ℂ, ‖t‖ ≤ R + 1 → (∀ b ∈ Branch, s b ≤ dist t b) →
      ∃ V, Good V ∧ Metric.ball t δ ⊆ V := by
  classical
  set K : Set ℂ := {t | ‖t‖ ≤ R + 1 ∧ ∀ b ∈ Branch, s b ≤ dist t b} with hK_def
  have hKsub : K ⊆ Metric.closedBall 0 (R + 1) := fun t ht => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ht.1
  have hKclosed : IsClosed K := by
    have h1 : K = {t : ℂ | ‖t‖ ≤ R + 1} ∩ ⋂ b ∈ Branch, {t : ℂ | s b ≤ dist t b} := by
      ext t
      simp [hK_def, Set.mem_iInter]
    rw [h1]
    refine IsClosed.inter ?_ (isClosed_biInter fun b _ => ?_)
    · exact isClosed_le continuous_norm continuous_const
    · exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) (R + 1)).of_isClosed_subset hKclosed hKsub
  have hV : ∀ k : K, ∃ V, IsOpen V ∧ (k : ℂ) ∈ V ∧ Good V := fun k =>
    hcover k.1 k.2.1 k.2.2
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hKcomp
    (c := fun k : K => (hV k).choose) (fun k => (hV k).choose_spec.1)
    (fun t ht => Set.mem_iUnion.mpr ⟨⟨t, ht⟩, (hV ⟨t, ht⟩).choose_spec.2.1⟩)
  refine ⟨δ, hδ, fun t h1 h2 => ?_⟩
  obtain ⟨k, hk⟩ := hball t ⟨h1, h2⟩
  exact ⟨(hV k).choose, (hV k).choose_spec.2.2, hk⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
