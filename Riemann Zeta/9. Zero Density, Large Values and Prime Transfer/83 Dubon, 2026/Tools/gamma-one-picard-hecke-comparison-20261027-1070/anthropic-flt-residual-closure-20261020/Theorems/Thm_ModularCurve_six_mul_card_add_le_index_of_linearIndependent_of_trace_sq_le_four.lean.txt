import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import P2M.Util
import P2M.Sol.S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four

open scoped MatrixGroups

theorem ModularCurve.six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four
    (N : ℕ) [NeZero N] (K : Type*) [Field K] {ι : Type*} [Fintype ι]
    (φ : ι → (Additive (CongruenceSubgroup.Gamma0 N) →+ K)) (hli : LinearIndependent K φ)
    (hφ : ∀ (i : ι) (γ : CongruenceSubgroup.Gamma0 N),
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 ≤ 4 → φ i (Additive.ofMul γ) = 0) :
    6 * Fintype.card ι + 6 * Nat.card (ModularCurve.CuspSpace N)
        + 3 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N // ModularGroup.S • x = x}
        + 4 * Nat.card {x : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N //
            (ModularGroup.S * ModularGroup.T) • x = x} ≤
      12 + (CongruenceSubgroup.Gamma0 N).index := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_six_mul_card_add_le_index_of_linearIndependent_of_trace_sq_le_four.solution
