import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_transcendental_jqModC

open ModularCurve
theorem ModularCurve.transcendental_jqModC (K : Type*) [CommRing K] :
    Transcendental K (jqModC K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_transcendental_jqModC.solution
