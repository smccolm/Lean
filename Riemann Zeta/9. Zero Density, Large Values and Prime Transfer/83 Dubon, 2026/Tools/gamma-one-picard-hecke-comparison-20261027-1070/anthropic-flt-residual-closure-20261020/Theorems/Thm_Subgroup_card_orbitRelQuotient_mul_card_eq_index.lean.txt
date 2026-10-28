import Mathlib
import P2M.Util
import P2M.Sol.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index

set_option autoImplicit false
theorem Subgroup.card_orbitRelQuotient_mul_card_eq_index {M : Type*} [Group M] (H K : Subgroup M)
    (hKH : ∀ g x : M, x ∈ K → g⁻¹ * x * g ∈ H → x = 1) :
    Nat.card (MulAction.orbitRel.Quotient H (M ⧸ K)) * Nat.card K = H.index := by p2m_exact_reverting @_root_.P2MW.S_Subgroup_card_orbitRelQuotient_mul_card_eq_index.solution
