import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_coeffMap_qExpand

theorem ModularCurve.coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) : ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand S n (ModularCurve.coeffMap f x) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffMap_qExpand.solution
