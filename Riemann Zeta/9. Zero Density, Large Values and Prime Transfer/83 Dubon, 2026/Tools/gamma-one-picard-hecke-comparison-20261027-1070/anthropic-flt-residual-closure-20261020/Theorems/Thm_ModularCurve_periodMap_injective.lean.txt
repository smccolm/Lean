import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_injective

open scoped MatrixGroups
theorem ModularCurve.periodMap_injective {N : ℕ} [NeZero N] :
    Function.Injective (ModularCurve.periodMap N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_injective.solution
