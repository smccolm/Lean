import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero

theorem WeierstrassCurve.mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₆ : E.a₆ = 0) (ha₄ : E.a₄ ≠ 0)
    (C : WeierstrassCurve.VariableChange F) :
    C ∈ MulAction.stabilizer (WeierstrassCurve.VariableChange F) E ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 4 = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_mem_stabilizer_variableChange_iff_of_isShortNF_of_a6_eq_zero.solution
