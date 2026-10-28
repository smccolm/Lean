import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isParabolicHom_apply_eq_period

theorem ModularCurve.exists_isParabolicHom_apply_eq_period (N : ℕ) [NeZero N] :
    ∃ Φ : Additive (CongruenceSubgroup.Gamma0 N) →+
        Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      ModularCurve.Period.IsParabolicHom (CongruenceSubgroup.Gamma0 N) Φ ∧
        ∀ γ : CongruenceSubgroup.Gamma0 N, Φ (Additive.ofMul γ) = ModularCurve.period N γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isParabolicHom_apply_eq_period.solution
