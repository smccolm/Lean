import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMapBundled
import P2M.Util
import P2M.Sol.S_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive

theorem ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitive N f F) (γ : CongruenceSubgroup.Gamma0 N) :
    ModularCurve.period N γ f =
      F ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • UpperHalfPlane.I) - F UpperHalfPlane.I := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive.solution
