import Mathlib
import P2M.Util
import P2M.Sol.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank

set_option autoImplicit false
theorem Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank {G : Fin 2 → Type*} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex]
    (hH : ∀ (i : Fin 2) (g : Monoid.CoprodI G) (x : G i), g⁻¹ * Monoid.CoprodI.of x * g ∈ H → x = 1) :
    Nonempty (FreeGroupBasis
      (Fin (1 + H.index - H.index / Nat.card (G 0) - H.index / Nat.card (G 1))) H) := by p2m_exact_reverting @_root_.P2MW.S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.solution
