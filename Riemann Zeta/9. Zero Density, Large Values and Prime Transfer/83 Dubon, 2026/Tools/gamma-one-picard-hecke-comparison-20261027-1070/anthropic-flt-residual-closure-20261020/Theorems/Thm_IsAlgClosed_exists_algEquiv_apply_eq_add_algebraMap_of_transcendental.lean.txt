import Mathlib
import P2M.Util
import P2M.Sol.S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental

theorem IsAlgClosed.exists_algEquiv_apply_eq_add_algebraMap_of_transcendental
    (K K' : Type*) [Field K] [Field K'] [Algebra K K'] [IsAlgClosed K']
    (t : K') (ht : Transcendental K t) (a : K) :
    ∃ τ : K' ≃ₐ[K] K', τ t = t + algebraMap K K' a := by p2m_exact_reverting @_root_.P2MW.S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental.solution
