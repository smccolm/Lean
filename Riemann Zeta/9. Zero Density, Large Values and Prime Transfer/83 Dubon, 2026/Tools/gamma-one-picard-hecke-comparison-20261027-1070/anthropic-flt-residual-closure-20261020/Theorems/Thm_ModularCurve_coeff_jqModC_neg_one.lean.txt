import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_jqModC_neg_one

open ModularCurve
theorem ModularCurve.coeff_jqModC_neg_one (K : Type*) [CommRing K] :
    (jqModC K).coeff (-1 : ℤ) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_jqModC_neg_one.solution
