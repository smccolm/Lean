import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_smul

open scoped MatrixGroups
theorem ModularCurve.periodMap_smul {N : ℕ} (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N (c • f) = c • ModularCurve.periodMap N f := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_smul.solution
