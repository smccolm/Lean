import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_frobenius_identity_geom_unconditional

open ModularCurve
theorem ModularCurve.frobenius_identity_geom_unconditional (K : Type*) [CommRing K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] :
    jqNModC K ℓ = (jqModC K) ^ ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frobenius_identity_geom_unconditional.solution
