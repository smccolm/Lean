import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isAlgClosed_residueField

theorem ValuationSubring.isAlgClosed_residueField {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : IsAlgClosed (IsLocalRing.ResidueField A) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField.solution
