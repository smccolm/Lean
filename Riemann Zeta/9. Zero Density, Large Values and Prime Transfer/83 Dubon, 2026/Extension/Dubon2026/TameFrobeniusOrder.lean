/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Subgroup_exists_wild_tame_cyclic_unramified_chain_of_le.lean.
Modified to isolate the finite Frobenius order argument at default proof limits.
This proves prime-to-residue-characteristic tame order for DUB-17's auxiliary local condition.
-/
import Mathlib.GroupTheory.OrderOfElement

namespace Dubon2026

theorem finite_frobenius_relation_order_coprime
    {G : Type*} [Group G] [Finite G] (p : ℕ) (hp : p.Prime) (φ t : G)
    (hφ : φ * t * φ⁻¹ = t ^ p) : Nat.Coprime p (orderOf t) := by
  have he : orderOf (t ^ p) = orderOf t := by
    rw [← hφ, ← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj φ).toMonoidHom (MulAut.conj φ).injective t
  rw [orderOf_pow' t hp.ne_zero] at he
  have hg : Nat.gcd (orderOf t) p = 1 := by
    rcases Nat.div_eq_self.mp he with h | h
    · exact absurd h (orderOf_pos t).ne'
    · exact h
  exact Nat.coprime_comm.mp hg

end Dubon2026
