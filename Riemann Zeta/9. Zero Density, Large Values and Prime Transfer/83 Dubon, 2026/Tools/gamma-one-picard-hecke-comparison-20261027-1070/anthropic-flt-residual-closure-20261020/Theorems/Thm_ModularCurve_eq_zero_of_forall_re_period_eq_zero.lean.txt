import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_eq_zero_of_forall_re_period_eq_zero
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

theorem ModularCurve.eq_zero_of_forall_re_period_eq_zero (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (h : ∀ γ : CongruenceSubgroup.Gamma0 N, (ModularCurve.period N γ f).re = 0) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_eq_zero_of_forall_re_period_eq_zero.solution
