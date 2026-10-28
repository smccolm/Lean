import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime

open OnePoint
theorem ModularCurve.ratPoint_eq_ratPoint_iff_of_isCoprime {a c a' c' : ℤ} (h : IsCoprime a c)
    (h' : IsCoprime a' c') :
    ModularCurve.ratPoint a c = ModularCurve.ratPoint a' c' ↔ (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.solution
