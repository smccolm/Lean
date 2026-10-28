import Mathlib
import P2M.Util
import P2M.Sol.S_SimpleGraph_exists_walkConnected_transversal_of_preconnected

set_option autoImplicit false
theorem SimpleGraph.exists_walkConnected_transversal_of_preconnected {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧
      (∀ v ∈ D, ∀ w ∈ D, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ D) ∧
      (∀ v ∈ D, ∀ w ∈ D, v ∈ MulAction.orbit Γ w → v = w) ∧
      (∀ u : V, ∃ v ∈ D, v ∈ MulAction.orbit Γ u) := by p2m_exact_reverting @_root_.P2MW.S_SimpleGraph_exists_walkConnected_transversal_of_preconnected.solution
