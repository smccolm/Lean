import Mathlib
import P2M.Util
import P2M.Sol.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve

theorem MulAction.natCard_fixedBy_of_isPretransitive_of_card_eq_twelve
    {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 12)
    (hG' : ∀ g : G, g ^ 2 = 1 ∨ g ^ 3 = 1)
    (X : Type*) [MulAction G X] [Nonempty X] [MulAction.IsPretransitive G X] :
    (Nat.card X = 1 ∨ Nat.card X = 3 ∨ Nat.card X = 4 ∨ Nat.card X = 6 ∨ Nat.card X = 12) ∧
    (∀ a : G, a ≠ 1 → a ^ 2 = 1 →
      (Nat.card X = 1 → Nat.card (MulAction.fixedBy X a) = 1) ∧
      (Nat.card X = 3 → Nat.card (MulAction.fixedBy X a) = 3) ∧
      (Nat.card X = 4 → Nat.card (MulAction.fixedBy X a) = 0) ∧
      (Nat.card X = 6 → Nat.card (MulAction.fixedBy X a) = 2) ∧
      (Nat.card X = 12 → Nat.card (MulAction.fixedBy X a) = 0)) ∧
    (∀ b : G, b ≠ 1 → b ^ 3 = 1 →
      (Nat.card X = 1 → Nat.card (MulAction.fixedBy X b) = 1) ∧
      (Nat.card X = 3 → Nat.card (MulAction.fixedBy X b) = 0) ∧
      (Nat.card X = 4 → Nat.card (MulAction.fixedBy X b) = 1) ∧
      (Nat.card X = 6 → Nat.card (MulAction.fixedBy X b) = 0) ∧
      (Nat.card X = 12 → Nat.card (MulAction.fixedBy X b) = 0)) := by p2m_exact_reverting @_root_.P2MW.S_MulAction_natCard_fixedBy_of_isPretransitive_of_card_eq_twelve.solution
