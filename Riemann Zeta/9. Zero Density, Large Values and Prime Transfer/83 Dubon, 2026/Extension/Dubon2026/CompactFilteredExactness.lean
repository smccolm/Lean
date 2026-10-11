import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact

/-! # Actual exact solutions from original compact filtered approximations -/

namespace Dubon2026

/-- A continuous map from the original compact space has an exact preimage
when its original image meets every set in a nested closed family whose
intersection is the displayed singleton. -/
theorem compact_exists_of_nested_closed_image_approximations
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (C : ℕ → Set Y)
    (hC : ∀ n, IsClosed (C n)) (hmono : ∀ n, C (n + 1) ⊆ C n)
    (y : Y) (hsep : (⋂ n, C n) = {y}) (happrox : ∀ n, ∃ x, f x ∈ C n) :
    ∃ x, f x = y := by
  let F : ℕ → Set X := fun n => f ⁻¹' C n
  have hF (n : ℕ) : IsClosed (F n) := (hC n).preimage hf
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F
    (fun n _ hx => hmono n hx) (fun n => happrox n) (hF 0).isCompact hF
  have h : f x ∈ ⋂ n, C n := by
    exact Set.mem_iInter.mpr (fun n => Set.mem_iInter.mp hx n)
  rw [hsep] at h
  exact ⟨x, h⟩

/-- Original additive approximation modulo a separating closed subgroup
filtration yields an exact original solution by compactness. This supplies a
limit step only; the actual finite-stage corrections must still be proved. -/
theorem compact_exists_of_additive_filtered_approximations
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    (f : X → Y) (hf : Continuous f) (F : ℕ → AddSubgroup Y)
    (hF : ∀ n, IsClosed (F n : Set Y)) (hmono : ∀ n, F (n + 1) ≤ F n)
    (hsep : ∀ z : Y, (∀ n, z ∈ F n) → z = 0)
    (y : Y) (happrox : ∀ n, ∃ x, f x - y ∈ F n) : ∃ x, f x = y := by
  apply compact_exists_of_nested_closed_image_approximations f hf
    (fun n => {z | z - y ∈ F n})
    (fun n => (hF n).preimage (continuous_id.sub continuous_const))
    (fun n _ hx => hmono n hx) y ?_ happrox
  ext z
  simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hz
    exact sub_eq_zero.mp (hsep (z - y) hz)
  · rintro rfl
    simp

end Dubon2026
