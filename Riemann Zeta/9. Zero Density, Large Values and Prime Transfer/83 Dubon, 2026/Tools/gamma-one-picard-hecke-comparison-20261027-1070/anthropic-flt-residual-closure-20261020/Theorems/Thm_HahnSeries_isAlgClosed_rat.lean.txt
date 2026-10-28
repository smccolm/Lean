import Mathlib
import P2M.Util
import P2M.Sol.S_HahnSeries_isAlgClosed_rat

theorem HahnSeries.isAlgClosed_rat {K : Type*} [Field K] [IsAlgClosed K] :
    IsAlgClosed (HahnSeries ℚ K) := by p2m_exact_reverting @_root_.P2MW.S_HahnSeries_isAlgClosed_rat.solution
