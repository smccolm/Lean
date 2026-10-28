import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_discriminant_ne_zero

theorem PeriodPair.discriminant_ne_zero (L : PeriodPair) : L.DiscriminantNeZero := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_discriminant_ne_zero.solution
