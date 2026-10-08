import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Genuine orthogonal projections onto invariant subspaces of an original unitary action -/

namespace Dubon2026

noncomputable section

variable {G V : Type*} [Group G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The original orthogonal complement of an invariant subspace is invariant under a genuine unitary group action. -/
theorem unitary_invariant_orthogonal (ρ : Representation ℂ G V)
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    (p : Submodule ℂ V) (hp : ∀ g v, v ∈ p → ρ g v ∈ p)
    (g : G) (v : V) (hv : v ∈ pᗮ) : ρ g v ∈ pᗮ := by
  intro u hu
  have he : ρ g (ρ g⁻¹ u) = u := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
    map_one, Module.End.one_apply]
  rw [← he, hunit]
  exact hv (ρ g⁻¹ u) (hp g⁻¹ u hu)

/-- The actual orthogonal projection onto an invariant original subspace commutes with the genuine unitary action. -/
theorem unitary_invariant_starProjection (ρ : Representation ℂ G V)
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    (p : Submodule ℂ V) [p.HasOrthogonalProjection]
    (hp : ∀ g v, v ∈ p → ρ g v ∈ p) (g : G) (v : V) :
    p.starProjection (ρ g v) = ρ g (p.starProjection v) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hp g _ (p.starProjection_apply_mem v)
  · rw [← map_sub]
    exact unitary_invariant_orthogonal ρ hunit p hp g _ (p.sub_starProjection_mem_orthogonal v)

end
end Dubon2026
