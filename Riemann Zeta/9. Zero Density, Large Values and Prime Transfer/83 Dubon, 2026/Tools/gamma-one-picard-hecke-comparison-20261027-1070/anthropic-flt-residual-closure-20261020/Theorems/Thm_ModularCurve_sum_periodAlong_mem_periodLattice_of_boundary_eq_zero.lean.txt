import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import P2M.Util
import P2M.Sol.S_ModularCurve_sum_periodAlong_mem_periodLattice_of_boundary_eq_zero
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one

open UpperHalfPlane
open scoped MatrixGroups

open Classical in

theorem ModularCurve.sum_periodAlong_mem_periodLattice_of_boundary_eq_zero
    {N : ℕ} [NeZero N] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ,
      Z.sum (fun e m =>
        (if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
        (if ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • e.1 = τ then m else 0)) = 0) :
    (Z.sum fun e m => m • ModularCurve.periodAlong N e.1 e.2) ∈
      ModularCurve.periodLattice N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_sum_periodAlong_mem_periodLattice_of_boundary_eq_zero.solution
