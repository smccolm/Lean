import Dubon2026.UnitaryInvariantProjection
import Mathlib.RepresentationTheory.Invariants

/-! # Actual fixed-vector projection preserves every closed unitary invariant subspace -/

namespace Dubon2026

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Orthogonal projections commute when one genuinely preserves the other's original range. -/
theorem starProjection_commute_of_preserves (p q : Submodule ℂ V)
    [p.HasOrthogonalProjection] [q.HasOrthogonalProjection]
    (hpq : ∀ w ∈ q, p.starProjection w ∈ q) (v : V) :
    q.starProjection (p.starProjection v) = p.starProjection (q.starProjection v) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hpq _ (q.starProjection_apply_mem v)
  · rw [← map_sub]
    intro u hu
    rw [← Submodule.inner_starProjection_left_eq_right]
    exact q.sub_starProjection_mem_orthogonal v _ (hpq u hu)

/-- The genuine orthogonal projection onto actual group-fixed vectors preserves every original closed invariant subspace. -/
theorem invariantProjection_mem_invariant_submodule {G : Type*} [Group G]
    (ρ : Representation ℂ G V)
    (hunit : ∀ g v w, inner ℂ (ρ g v) (ρ g w) = inner ℂ v w)
    (p : Submodule ℂ V) [p.HasOrthogonalProjection] [ρ.invariants.HasOrthogonalProjection]
    (hp : ∀ g v, v ∈ p → ρ g v ∈ p) (v : V) (hv : v ∈ p) :
    ρ.invariants.starProjection v ∈ p := by
  have hpq : ∀ w ∈ ρ.invariants, p.starProjection w ∈ ρ.invariants := by
    intro w hw
    rw [Representation.mem_invariants] at hw ⊢
    intro g
    rw [← unitary_invariant_starProjection ρ hunit p hp g w, hw g]
  have he := starProjection_commute_of_preserves p ρ.invariants hpq v
  rw [p.starProjection_eq_self_iff.mpr hv] at he
  exact he.symm ▸ p.starProjection_apply_mem (ρ.invariants.starProjection v)

end
end Dubon2026
