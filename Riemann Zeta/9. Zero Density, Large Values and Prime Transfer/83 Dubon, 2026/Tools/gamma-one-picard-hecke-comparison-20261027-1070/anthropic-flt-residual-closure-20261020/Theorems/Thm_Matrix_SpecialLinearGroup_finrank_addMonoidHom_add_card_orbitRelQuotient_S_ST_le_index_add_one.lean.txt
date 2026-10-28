import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one

set_option autoImplicit false
theorem Matrix.SpecialLinearGroup.finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ) (K : Type) [Field K]
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    Module.finrank K (Additive Γ →+ K)
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers ModularGroup.S)
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      + Nat.card (MulAction.orbitRel.Quotient (Subgroup.zpowers (ModularGroup.S * ModularGroup.T))
          (Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Γ))
      ≤ Γ.index + 1 := by p2m_exact_reverting @_root_.P2MW.S_Matrix_SpecialLinearGroup_finrank_addMonoidHom_add_card_orbitRelQuotient_S_ST_le_index_add_one.solution
