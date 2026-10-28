import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_periodAlong_smul_sub_periodAlong_eq_period
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.periodAlong_smul_sub_periodAlong_eq_period
    (N : ℕ) [NeZero N] (γ : CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    ModularCurve.periodAlong N UpperHalfPlane.I ((γ : SL(2, ℤ)) • τ) -
      ModularCurve.periodAlong N UpperHalfPlane.I τ = ModularCurve.period N γ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_periodAlong_smul_sub_periodAlong_eq_period.solution
