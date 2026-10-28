import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount

open OnePoint
theorem ModularCurve.CuspSpace.card_cuspSpace_eq_cuspCount {N : ℕ} (hN : N ≠ 0) :
    Nat.card (ModularCurve.CuspSpace N) = ModularCurve.cuspCount N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_card_cuspSpace_eq_cuspCount.solution
