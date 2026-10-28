import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_dedekindPsi_prime

open ModularCurve IntermediateField
theorem ModularCurve.dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dedekindPsi_prime.solution
