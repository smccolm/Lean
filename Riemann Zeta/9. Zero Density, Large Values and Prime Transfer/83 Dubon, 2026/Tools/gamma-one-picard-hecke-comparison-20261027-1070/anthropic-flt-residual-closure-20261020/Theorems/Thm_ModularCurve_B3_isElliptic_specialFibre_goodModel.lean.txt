import Definitions.Def_ModularCurve_SpecialisationVocab
import Definitions.Def_ModularCurve_TatePoint
import P2M.Util
import P2M.Sol.S_ModularCurve_B3_isElliptic_specialFibre_goodModel

open ModularCurve.TatePoint
theorem ModularCurve.B3.isElliptic_specialFibre_goodModel (j₀ : Qbar) :
    (specialFibre (goodModel j₀)).IsElliptic := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_B3_isElliptic_specialFibre_goodModel.solution
