import Dubon2026.CoefficientRepresentationColimit
import Mathlib.Topology.Algebra.Module.Basic

/-! # Compact cochains lift to a stage of the actual coefficient colimit

This finite-image lifting and common zero detection are used to descend
continuous arithmetic class H1 to the proved finite-stage class quotient
H1. That removes the first global class-formation premise on DUB-17's
localization exactness route; no higher-degree generalization is selected.
-/

namespace Dubon2026
noncomputable section

variable {R ι : Type} [CommRing R] [Preorder ι] [DecidableEq ι]
  [Nonempty ι] [IsDirectedOrder ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)

/-- A continuous compact-domain cochain in the discrete coefficient colimit lifts continuously to one original stage. -/
theorem compactCoefficientColimit_exists_lift
    [TopologicalSpace (Module.DirectLimit M f)] [DiscreteTopology (Module.DirectLimit M f)]
    [∀ i, TopologicalSpace (M i)] [∀ i, DiscreteTopology (M i)]
    {X : Type} [TopologicalSpace X] [CompactSpace X]
    (b : X → Module.DirectLimit M f) (hb : Continuous b) :
    ∃ i, ∃ c : X → M i, Continuous c ∧
      ∀ x, Module.DirectLimit.of R ι M f i (c x) = b x := by
  classical
  have hr : (Set.range b).Finite := (isCompact_range hb).finite_of_discrete
  choose i y hy using (fun z : Module.DirectLimit M f => Module.DirectLimit.exists_of z)
  obtain ⟨j, hj⟩ := (hr.toFinset.image i).exists_le
  have hij (z : Module.DirectLimit M f) (hz : z ∈ Set.range b) : i z ≤ j :=
    hj (i z) (Finset.mem_image.mpr ⟨z, hr.mem_toFinset.mpr hz, rfl⟩)
  let l : Module.DirectLimit M f → M j := fun z =>
    if hz : z ∈ Set.range b then f (i z) j (hij z hz) (y z) else 0
  refine ⟨j, l ∘ b, continuous_of_discreteTopology.comp hb, ?_⟩
  intro x
  change Module.DirectLimit.of R ι M f j (l (b x)) = b x
  dsimp only [l]
  rw [dif_pos (Set.mem_range_self x), Module.DirectLimit.of_f]
  exact hy (b x)

/-- A finite set of actual stage coefficients killed in the colimit is killed together at a single larger stage. -/
theorem coefficientColimit_finite_zero_detected
    [DirectedSystem M (fun i j h => f i j h)]
    (i : ι) (T : Finset (M i))
    (hT : ∀ x ∈ T, Module.DirectLimit.of R ι M f i x = 0) :
    ∃ j, ∃ hij : i ≤ j, ∀ x ∈ T, f i j hij x = 0 := by
  classical
  have hz (x : T) : ∃ j, ∃ hij : i ≤ j, f i j hij x.val = 0 :=
    Module.DirectLimit.of.zero_exact (hT x.val x.property)
  choose j hij hj using hz
  obtain ⟨k, hk⟩ := (insert i (Finset.univ.image j)).exists_le
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  have hjk (x : T) : j x ≤ k := hk (j x)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩))
  refine ⟨k, hik, ?_⟩
  intro x hx
  let z : T := ⟨x, hx⟩
  have hc := Module.DirectedSystem.map_map f (hij z) (hjk z) x
  rw [hj z, map_zero] at hc
  exact hc.symm

end
end Dubon2026
