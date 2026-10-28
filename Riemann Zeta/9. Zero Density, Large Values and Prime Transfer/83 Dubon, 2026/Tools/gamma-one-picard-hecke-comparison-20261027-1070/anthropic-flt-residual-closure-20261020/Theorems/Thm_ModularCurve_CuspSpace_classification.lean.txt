import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_CuspSpace_classification

open OnePoint
theorem ModularCurve.CuspSpace.classification {N : ℕ} (hN : N ≠ 0) :
    ModularCurve.CuspSpace.Classification N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_classification.solution
