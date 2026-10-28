import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_isUniformization_toPoint

theorem PeriodPair.isUniformization_toPoint (L : PeriodPair) (h : L.DiscriminantNeZero) :
    L.IsUniformization h := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_isUniformization_toPoint.solution
