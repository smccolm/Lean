import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_le_forall_mem_iff_apply_mem

theorem ValuationSubring.exists_le_forall_mem_iff_apply_mem
    {F : Type*} [Field F] (O : ValuationSubring F)
    {Kbar : Type*} [Field Kbar] (res : O →+* Kbar)
    (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res)
    (W : ValuationSubring Kbar) :
    ∃ O' : ValuationSubring F, O' ≤ O ∧
      (∀ x : O, (x : F) ∈ O' ↔ res x ∈ W) ∧
      (∀ x : O, (x : F) ∈ O'.nonunits ↔ res x ∈ W.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_le_forall_mem_iff_apply_mem.solution
