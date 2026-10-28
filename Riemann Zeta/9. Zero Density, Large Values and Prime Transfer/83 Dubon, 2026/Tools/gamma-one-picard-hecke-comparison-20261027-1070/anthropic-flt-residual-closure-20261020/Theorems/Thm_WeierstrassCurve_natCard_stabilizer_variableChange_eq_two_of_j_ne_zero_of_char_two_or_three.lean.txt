import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
    {F : Type*} [Field F] (hF : ringChar F = 2 ∨ ringChar F = 3)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three.solution
