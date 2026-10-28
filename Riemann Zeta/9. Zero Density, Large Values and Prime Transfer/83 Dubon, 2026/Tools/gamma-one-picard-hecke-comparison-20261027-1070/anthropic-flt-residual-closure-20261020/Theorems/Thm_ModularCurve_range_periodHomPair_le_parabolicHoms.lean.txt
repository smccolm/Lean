import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import P2M.Util
import P2M.Sol.S_ModularCurve_range_periodHomPair_le_parabolicHoms

set_option autoImplicit false
theorem ModularCurve.range_periodHomPair_le_parabolicHoms (N : ℕ) [NeZero N] :
    LinearMap.range (ModularCurve.periodHomPair N)
      ≤ ModularCurve.Period.parabolicHoms ℂ (CongruenceSubgroup.Gamma0 N) ℂ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_range_periodHomPair_le_parabolicHoms.solution
