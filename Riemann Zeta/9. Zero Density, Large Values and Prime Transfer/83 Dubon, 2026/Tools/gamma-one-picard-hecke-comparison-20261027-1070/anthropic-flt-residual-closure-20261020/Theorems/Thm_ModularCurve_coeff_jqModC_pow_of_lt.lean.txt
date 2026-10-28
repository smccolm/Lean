import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_jqModC_pow_of_lt

open ModularCurve
theorem ModularCurve.coeff_jqModC_pow_of_lt (K : Type*) [CommRing K] {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqModC K) ^ b).coeff m = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_jqModC_pow_of_lt.solution
