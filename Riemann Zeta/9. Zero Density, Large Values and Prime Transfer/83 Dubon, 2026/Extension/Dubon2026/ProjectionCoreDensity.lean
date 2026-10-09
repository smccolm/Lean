import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! # Density of a genuine projection-stable core in the original fixed subspace -/

namespace Dubon2026

noncomputable section

/-- An actual orthogonal projector preserving an original linear core makes the core's fixed part dense in the fixed part of its original closure. -/
theorem projection_stable_core_closure {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (p q : Submodule ℂ V) [q.HasOrthogonalProjection] (hq : IsClosed (q : Set V))
    (hp : ∀ v ∈ p, q.starProjection v ∈ p) :
    (p ⊓ q).topologicalClosure = p.topologicalClosure ⊓ q := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · intro v hv
      exact ⟨Submodule.le_topologicalClosure p hv.1, hv.2⟩
    · exact p.isClosed_topologicalClosure.inter hq
  · rintro v ⟨hvp, hvq⟩
    have hs : ∀ w ∈ p, q.starProjection w ∈ (p ⊓ q).topologicalClosure := by
      intro w hw
      exact Submodule.le_topologicalClosure _ ⟨hp w hw, q.starProjection_apply_mem w⟩
    have hv := closure_minimal hs ((p ⊓ q).isClosed_topologicalClosure.preimage
      q.starProjection.continuous) hvp
    change q.starProjection v ∈ (p ⊓ q).topologicalClosure at hv
    rwa [q.starProjection_eq_self_iff.mpr hvq] at hv

end
end Dubon2026
