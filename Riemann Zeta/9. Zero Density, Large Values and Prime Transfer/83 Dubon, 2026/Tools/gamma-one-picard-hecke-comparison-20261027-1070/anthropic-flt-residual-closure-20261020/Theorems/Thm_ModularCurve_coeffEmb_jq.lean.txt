import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffEmb_jq

open ModularCurve
theorem ModularCurve.coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] :
    coeffEmb L jq = jqModC L := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_jq.solution
