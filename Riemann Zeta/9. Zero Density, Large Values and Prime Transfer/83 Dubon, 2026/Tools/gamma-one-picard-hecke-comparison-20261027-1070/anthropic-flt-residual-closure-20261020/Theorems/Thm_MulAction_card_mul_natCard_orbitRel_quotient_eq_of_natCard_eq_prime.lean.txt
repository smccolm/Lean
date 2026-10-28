import Mathlib
import P2M.Util
import P2M.Sol.S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime

theorem MulAction.card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime
    (G : Type*) {X : Type*} [Group G] [MulAction G X] [Finite G] [Finite X]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p) :
    p * Nat.card (MulAction.orbitRel.Quotient G X)
      = Nat.card X + (p - 1) * Nat.card (MulAction.fixedPoints G X) := by p2m_exact_reverting @_root_.P2MW.S_MulAction_card_mul_natCard_orbitRel_quotient_eq_of_natCard_eq_prime.solution
