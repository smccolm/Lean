import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_periodMap_mem_parabolicHoms

open scoped MatrixGroups
theorem ModularCurve.periodMap_mem_parabolicHoms {N : ℕ} (R : Type*) [Semiring R] [Module R ℂ]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    ModularCurve.periodMap N f ∈ ModularCurve.Period.parabolicHoms R (CongruenceSubgroup.Gamma0 N) ℂ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodMap_mem_parabolicHoms.solution
