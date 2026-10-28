import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_aeval_jq_eq_zero

open ModularCurve IntermediateField
theorem ModularCurve.aeval_jq_eq_zero {p : Polynomial ℚ} (hp : Polynomial.aeval jq p = 0) : p = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_aeval_jq_eq_zero.solution
