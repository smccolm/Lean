import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg

theorem ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) :
    ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap K L)) +
      (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.solution
