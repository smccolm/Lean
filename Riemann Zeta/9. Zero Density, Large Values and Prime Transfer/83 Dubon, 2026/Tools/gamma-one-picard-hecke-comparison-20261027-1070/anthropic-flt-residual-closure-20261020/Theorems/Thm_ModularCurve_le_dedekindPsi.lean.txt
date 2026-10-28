import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_le_dedekindPsi

open ModularCurve
theorem ModularCurve.le_dedekindPsi (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_le_dedekindPsi.solution
