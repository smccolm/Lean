import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_mem_of_forall_mem_iff_of_subset

theorem ValuationSubring.mem_of_forall_mem_iff_of_subset
    {F : Type*} [Field F] (K : Subfield F) (O V : ValuationSubring F)
    (hKV : ∀ e ∈ K, e ∈ O → e ∈ V) (g : F)
    (hg : ∀ V' : ValuationSubring F, (∀ e ∈ K, e ∈ V' ↔ e ∈ O) → g ∈ V') :
    g ∈ V := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_mem_of_forall_mem_iff_of_subset.solution
