import Dubon2026.CompactOpenOrbitFinite
import Mathlib.GroupTheory.Coset.Basic

/-! # Genuine finite coset traces in the original group representation -/

namespace Dubon2026

noncomputable section
open scoped BigOperators

/-- Summing an actual subgroup-fixed vector over a proved finite coset transversal produces a vector fixed by the entire original group. -/
theorem representation_coset_trace_invariant {G V ι : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [Fintype ι]
    (ρ : Representation ℂ G V) (H : Subgroup G) (v : V)
    (hv : ∀ h ∈ H, ρ h v = v) (r : ι → G) (e : ι ≃ G ⧸ H)
    (he : ∀ i, e i = QuotientGroup.mk (r i)) (g : G) :
    ρ g (∑ i, ρ (r i) v) = ∑ i, ρ (r i) v := by
  letI : Fintype (G ⧸ H) := Fintype.ofEquiv ι e
  let F : G ⧸ H → V := Quotient.lift (fun a => ρ a v) (by
    intro a b hab
    have hh : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h := congrArg (ρ a) (hv (a⁻¹ * b) hh)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h
    exact h.symm)
  have hF (q : G ⧸ H) : F (g • q) = ρ g (F q) := by
    induction q using Quotient.inductionOn with | h a => ?_
    change ρ (g * a) v = ρ g (ρ a v)
    rw [map_mul]
    rfl
  have hs : (∑ i, ρ (r i) v) = ∑ q : G ⧸ H, F q := by
    calc
      _ = ∑ i, F (e i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [he]
        rfl
      _ = _ := Equiv.sum_comp e F
  rw [hs, map_sum]
  simp_rw [← hF]
  exact Equiv.sum_comp (MulAction.toPerm g) F

end
end Dubon2026
