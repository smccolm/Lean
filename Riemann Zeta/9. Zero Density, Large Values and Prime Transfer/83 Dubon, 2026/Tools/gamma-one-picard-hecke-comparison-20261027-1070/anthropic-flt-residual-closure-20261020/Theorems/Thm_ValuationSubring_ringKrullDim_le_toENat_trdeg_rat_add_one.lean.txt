import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one

theorem ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    ringKrullDim A ≤ (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) + 1 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.solution
