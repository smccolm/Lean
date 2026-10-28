import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_injective

theorem ModularCurve.coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) : Function.Injective (ModularCurve.coeffMap f) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_injective.solution
