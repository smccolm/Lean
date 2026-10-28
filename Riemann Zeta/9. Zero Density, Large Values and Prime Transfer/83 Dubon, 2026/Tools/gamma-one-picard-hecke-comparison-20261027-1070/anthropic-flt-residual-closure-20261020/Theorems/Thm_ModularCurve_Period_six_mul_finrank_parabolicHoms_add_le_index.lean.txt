import Mathlib
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_ModularCurve_CuspSpace
import P2M.Util
import P2M.Sol.S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index

open scoped MatrixGroups
theorem ModularCurve.Period.six_mul_finrank_parabolicHoms_add_le_index (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [CharZero K] :
    6 * Module.finrank K (ModularCurve.Period.parabolicHoms K (CongruenceSubgroup.Gamma0 N) K)
        + 6 * Nat.card (ModularCurve.CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.solution
