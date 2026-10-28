import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_pos

open ModularCurve
theorem ModularCurve.dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_pos.solution
