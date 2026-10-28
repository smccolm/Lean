import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728

open ModularCurve.TatePoint
theorem ModularCurve.B3.nearCurve_eq_ofJNe0Or1728 (j₀ : Qbar) :
    nearCurve j₀ = WeierstrassCurve.ofJNe0Or1728 (jNear j₀) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_nearCurve_eq_ofJNe0Or1728.solution
