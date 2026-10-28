import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_transcendental_jq

open ModularCurve IntermediateField
theorem ModularCurve.transcendental_jq : Transcendental ℚ jq := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_transcendental_jq.solution
