import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat

theorem ValuationSubring.krullDimLE_one_of_isAlgebraic_rat
    {L : Type*} [Field L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] (A : ValuationSubring L) :
    Ring.KrullDimLE 1 A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat.solution
