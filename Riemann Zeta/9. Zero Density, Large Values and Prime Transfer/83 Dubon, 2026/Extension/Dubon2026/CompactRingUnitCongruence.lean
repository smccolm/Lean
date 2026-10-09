import Dubon2026.CompactRingIntegerIdeals
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Ring

/-! # Actual integer congruences are cofinal in the unit topology of the original compact ring -/

namespace Dubon2026

noncomputable section
open Filter Set Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CompactSpace R] [T2Space R] [Infinite R]

omit [Infinite R] in
/-- In the actual compact-ring unit topology, coercion to the original ring is a closed embedding. -/
theorem compactRing_units_val_isClosedEmbedding :
    IsClosedEmbedding (Units.val : Rˣ → R) :=
  Units.continuous_val.isClosedEmbedding Units.val_injective

/-- Every genuine unit identity neighborhood contains all original units congruent to one modulo some positive ordinary integer. -/
theorem compactRing_unit_congruence_small (hd : DenseRange (Int.cast : ℤ → R))
    (W : Set Rˣ) (hW : W ∈ 𝓝 1) :
    ∃ D : ℕ, 0 < D ∧ ∀ u : Rˣ, (D : R) ∣ u.val - 1 → u ∈ W := by
  have he := (compactRing_units_val_isClosedEmbedding (R := R)).toIsEmbedding.toIsInducing
  rw [he.nhds_eq_comap] at hW
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.mp hW
  have h0 : (fun x : R => 1 + x) ⁻¹' V ∈ 𝓝 0 := by
    have hc : ContinuousAt (fun x : R => 1 + x) 0 := (continuous_const.add continuous_id).continuousAt
    exact hc (by simpa only [Units.val_one, add_zero] using hV)
  obtain ⟨D, hD, hs⟩ := compactRing_positive_integer_ideal_small hd _ h0
  refine ⟨D, hD, ?_⟩
  rintro u ⟨x, hx⟩
  apply hsub
  change u.val ∈ V
  have h := hs x
  change 1 + (D : R) * x ∈ V at h
  have hu : u.val = 1 + (D : R) * x := by rw [← hx]; ring
  rwa [← hu] at h

end
end Dubon2026
