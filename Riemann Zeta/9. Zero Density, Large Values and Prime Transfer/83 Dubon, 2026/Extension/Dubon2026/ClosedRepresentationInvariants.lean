import Mathlib.Analysis.Complex.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Analysis.Normed.Operator.Basic

/-! # The actual fixed-vector space of a bounded representation is closed -/

namespace Dubon2026

/-- Simultaneous fixed vectors of genuine continuous linear group operators form a closed original subspace. -/
theorem representation_invariants_isClosed {G V : Type*} [Group G]
    [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ G V)
    (T : G → V →L[ℂ] V) (hT : ∀ g v, T g v = ρ g v) :
    IsClosed (ρ.invariants : Set V) := by
  have he : (ρ.invariants : Set V) = ⋂ g : G, {v : V | T g v = v} := by
    ext v
    simp only [Set.mem_iInter, Set.mem_setOf_eq, hT]
    rfl
  rw [he]
  exact isClosed_iInter (fun g => isClosed_eq (T g).continuous continuous_id)

end Dubon2026
