import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_natDegree_map_eq_card_roots_of_splits

open scoped Polynomial

theorem ValuationSubring.natDegree_map_eq_card_roots_of_splits
    {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
    (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (p : A[X]) (hp : p.map σ ≠ 0)
    (hsplit : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree) :
    (p.map σ).natDegree = Multiset.card p.roots := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_natDegree_map_eq_card_roots_of_splits.solution
