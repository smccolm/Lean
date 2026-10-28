import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_finite_stabilizer_variableChange

theorem WeierstrassCurve.finite_stabilizer_variableChange (F : Type*) [Field F] (E : WeierstrassCurve F) [E.IsElliptic] : Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_finite_stabilizer_variableChange.solution
