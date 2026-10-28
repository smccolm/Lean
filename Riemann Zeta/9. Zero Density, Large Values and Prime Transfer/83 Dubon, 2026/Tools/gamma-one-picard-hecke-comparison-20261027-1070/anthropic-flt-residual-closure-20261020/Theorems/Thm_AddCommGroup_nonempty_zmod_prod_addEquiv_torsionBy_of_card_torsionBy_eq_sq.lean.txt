import Mathlib
import P2M.Util
import P2M.Sol.S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq

theorem AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    {A : Type*} [AddCommGroup A] {n : ℕ} (hn : n ≠ 0)
    (hcard : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ 2) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.solution
