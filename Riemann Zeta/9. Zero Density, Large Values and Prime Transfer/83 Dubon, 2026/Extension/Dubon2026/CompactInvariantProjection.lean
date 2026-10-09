import Dubon2026.CompactOpenOrbitFinite
import Dubon2026.InvariantProjectionPreservation
import Dubon2026.FiniteOrbitOfEigenSpan
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Original compact fixed-vector projection retains a genuine finite orbit span -/

namespace Dubon2026

noncomputable section

/-- The actual fixed-vector projector of a compact unitary group sends every vector with open stabilizer into the span of its own finite original orbit. -/
theorem compactInvariantProjection_mem_orbitSpan {G V : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ρ : Representation ℂ G V)
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    [ρ.invariants.HasOrthogonalProjection]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (v : V) (hv : ∀ g ∈ H, ρ g v = v) :
    ρ.invariants.starProjection v ∈ Submodule.span ℂ (Set.range (fun g => ρ g v)) := by
  let U := Submodule.span ℂ (Set.range (fun g => ρ g v))
  letI : FiniteDimensional ℂ U := compactOrbitSpan_finite_of_open_stabilizer ρ H hH v hv
  apply invariantProjection_mem_invariant_submodule ρ hunit U
    (fun g w hw => representationOrbitSpan_invariant ρ v g w hw)
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

end
end Dubon2026
