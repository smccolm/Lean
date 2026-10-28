import Mathlib.GroupTheory.Index
import P2M.Util
import P2M.Sol.S_MulAction_ncard_orbit_inter_orbit_mul_card

theorem MulAction.ncard_orbit_inter_orbit_mul_card {G : Type*} [Group G] {X : Type*} [MulAction G X] [Finite G] [MulAction.IsPretransitive G X] (H₁ H₂ : Subgroup G) (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (x₁ x₂ : X) : (MulAction.orbit H₁ x₁ ∩ MulAction.orbit H₂ x₂).ncard * Nat.card X = (MulAction.orbit H₁ x₁).ncard * (MulAction.orbit H₂ x₂).ncard := by p2m_exact_reverting @_root_.P2MW.S_MulAction_ncard_orbit_inter_orbit_mul_card.solution
