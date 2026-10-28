import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_jqModC_pow_self

open ModularCurve
theorem ModularCurve.coeff_jqModC_pow_self (K : Type*) [CommRing K] (b : ℕ) :
    ((jqModC K) ^ b).coeff (-(b : ℤ)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_jqModC_pow_self.solution
