import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

theorem ValuationSubring.exists_ringHom_extend_of_isAlgClosed
    {L Ω : Type*} [Field L] [Field Ω] [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.solution
