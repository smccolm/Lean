import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_order_jqModC

open ModularCurve
theorem ModularCurve.order_jqModC (K : Type*) [CommRing K] [Nontrivial K] :
    (jqModC K).order = -1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_order_jqModC.solution
