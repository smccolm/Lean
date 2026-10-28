import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_swapBivar_eq_of_evalSymm

open ModularCurve
theorem ModularCurve.swapBivar_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    swapBivar Φ = Φ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_swapBivar_eq_of_evalSymm.solution
