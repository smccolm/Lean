import Definitions.Def_ModularCurve_PeriodHomPair
import P2M.Util
import P2M.Sol.S_ModularCurve_existsPeriodMapLinear

theorem ModularCurve.existsPeriodMapLinear (N : ℕ) :
    ModularCurve.ExistsPeriodMapLinear N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_existsPeriodMapLinear.solution
