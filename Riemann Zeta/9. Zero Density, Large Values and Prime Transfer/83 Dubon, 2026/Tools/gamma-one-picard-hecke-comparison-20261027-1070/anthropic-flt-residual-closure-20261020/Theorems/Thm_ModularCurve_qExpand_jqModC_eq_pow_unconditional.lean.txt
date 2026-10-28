import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpand_jqModC_eq_pow_unconditional

open ModularCurve
theorem ModularCurve.qExpand_jqModC_eq_pow_unconditional (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    qExpand K ℓ (jqModC K) = (jqModC K) ^ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpand_jqModC_eq_pow_unconditional.solution
