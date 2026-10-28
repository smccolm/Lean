import Mathlib
import P2M.Util
import P2M.Sol.S_IsAddCyclic_of_squarefree_natCard

theorem IsAddCyclic.of_squarefree_natCard
    {A : Type*} [AddCommGroup A] (hA : Squarefree (Nat.card A)) : IsAddCyclic A := by p2m_exact_reverting @_root_.P2MW.S_IsAddCyclic_of_squarefree_natCard.solution
