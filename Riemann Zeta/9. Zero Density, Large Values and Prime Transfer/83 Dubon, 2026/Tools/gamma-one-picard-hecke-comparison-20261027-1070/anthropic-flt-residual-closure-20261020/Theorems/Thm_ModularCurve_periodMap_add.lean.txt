import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_add

open scoped MatrixGroups
theorem ModularCurve.periodMap_add {N : ℕ} (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (f + g) = ModularCurve.periodMap N f + ModularCurve.periodMap N g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_add.solution
