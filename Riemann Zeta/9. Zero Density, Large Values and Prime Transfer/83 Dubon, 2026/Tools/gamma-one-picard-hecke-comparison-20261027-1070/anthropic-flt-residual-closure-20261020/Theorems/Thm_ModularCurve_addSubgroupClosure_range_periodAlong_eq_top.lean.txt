import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_addSubgroupClosure_range_periodAlong_eq_top
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

theorem ModularCurve.addSubgroupClosure_range_periodAlong_eq_top (N : ℕ) [NeZero N] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlong N p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_addSubgroupClosure_range_periodAlong_eq_top.solution
