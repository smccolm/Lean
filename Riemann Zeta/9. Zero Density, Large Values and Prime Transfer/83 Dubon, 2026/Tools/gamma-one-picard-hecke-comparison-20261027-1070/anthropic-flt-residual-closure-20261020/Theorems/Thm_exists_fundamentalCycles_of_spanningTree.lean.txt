import Mathlib
import P2M.Util
import P2M.Sol.S_exists_fundamentalCycles_of_spanningTree

theorem exists_fundamentalCycles_of_spanningTree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (hd tl : E → V) (T : Finset E)
    (hTpath : ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ Z : E → E → ℤ,
      (∀ j, ∀ w, (∑ e with hd e = w, Z j e) = (∑ e with tl e = w, Z j e)) ∧
      (∀ j ∈ Tᶜ, ∀ j' ∈ Tᶜ, Z j j' = if j = j' then 1 else 0) ∧
      (∀ j ∈ T, Z j = 0) ∧
      ∀ {A : Type*} [inst : AddCommGroup A] (f : E → A),
        (∀ w, (∑ e with hd e = w, f e) = (∑ e with tl e = w, f e)) →
        ∀ e, f e = ∑ j ∈ Tᶜ, Z j e • f j := by p2m_exact_reverting @_root_.P2MW.S_exists_fundamentalCycles_of_spanningTree.solution
