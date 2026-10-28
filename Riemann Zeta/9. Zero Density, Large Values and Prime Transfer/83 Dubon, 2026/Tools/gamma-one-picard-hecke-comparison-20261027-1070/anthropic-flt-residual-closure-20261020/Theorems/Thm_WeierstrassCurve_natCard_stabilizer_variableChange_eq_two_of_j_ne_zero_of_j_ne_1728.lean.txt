import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728

theorem WeierstrassCurve.natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728.solution
