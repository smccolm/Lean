import Mathlib
import P2M.Util
import P2M.Sol.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one

set_option autoImplicit false
theorem Monoid.CoprodI.finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
    {G : Fin 2 → Type*} [∀ i, Group (G i)]
    (H : Subgroup (Monoid.CoprodI G)) [H.FiniteIndex] (K : Type) [Field K]
    (hK : ∀ i, (Nat.card (G i) : K) ≠ 0) :
    Module.finrank K (Additive H →+ K)
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 0)).range))
      + Nat.card (MulAction.orbitRel.Quotient H
          (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := 1)).range))
      ≤ H.index + 1 := by p2m_exact_reverting @_root_.P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one.solution
