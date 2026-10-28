import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j

open WeierstrassCurve

theorem WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j
    {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 24) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j.solution
