import Dubon2026.AdelicRealCyclicClosure
import Dubon2026.AdelicClosedInvariantSpan

/-! # Irreducibility of the genuine original real cyclic Hilbert representation -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual original real group representation restricted to its literal closed cyclic Hilbert subspace. -/
def adelicRealCyclicRepresentation : Representation ℂ SL(2, ℝ) (adelicRealCyclicClosedSpan f) :=
  Representation.subrepresentation ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (adelicRealCyclicClosedSpan f) (fun g v hv => adelicRealCyclicClosedSpan_invariant f g v hv)

/-- The restricted real cyclic representation acts by exactly the original Hilbert group action. -/
theorem adelicRealCyclicRepresentation_apply (g : SL(2, ℝ)) (v : adelicRealCyclicClosedSpan f) :
    (adelicRealCyclicRepresentation f g v).val =
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v.val := rfl

/-- The actual real cyclic Hilbert space of a nonzero original cusp form is nonzero. -/
theorem adelicRealCyclicClosedSpan_ne_bot (hf : f ≠ 0) : adelicRealCyclicClosedSpan f ≠ ⊥ := by
  intro h
  have hm := adelicRealCyclicClosedSpan_orbit_mem f 1
  simp only [map_one, Module.End.one_apply, h, Submodule.mem_bot] at hm
  exact adelicCyclicHilbertGenerator_ne_zero f hf hm

/-- For every nonzero positive-weight original cusp form, its genuine real cyclic Hilbert space has no nonzero proper closed real-invariant subspace. -/
theorem adelicRealCyclicClosedSpan_irreducible (hf : f ≠ 0) (hk : 0 < k)
    (p : Submodule ℂ (AdelicCyclicHilbert f)) (hp : IsClosed (p : Set (AdelicCyclicHilbert f)))
    (hle : p ≤ adelicRealCyclicClosedSpan f)
    (hinv : ∀ g : SL(2, ℝ), ∀ v ∈ p,
      adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v ∈ p) :
    p = ⊥ ∨ p = adelicRealCyclicClosedSpan f := by
  have he := adelicRaisingClosedSpan_eq_realCyclicClosedSpan f hf
  have hr := adelicRaisingClosedSpan_invariant_eq_bot_or_eq f hf hk p hp (he ▸ hle) hinv
  exact hr.imp id (fun h => h.trans he)

end
end Dubon2026
